/*
 * Copyright (c)2013-2021 ZeroTier, Inc.
 *
 * Use of this software is governed by the Business Source License included
 * in the LICENSE.TXT file in the project's root directory.
 *
 * Change Date: 2026-01-01
 *
 * On the date above, in accordance with the Business Source License, use
 * of this software will be governed by version 2.0 of the Apache License.
 */
/****/

#include "Bond.hpp"

#include "../osdep/OSUtils.hpp"
#include "Switch.hpp"

#include <cmath>

namespace ZeroTier {

Bond::Bond(const RuntimeEnvironment* renv, int policy, const SharedPtr<Peer>& peer)
	: RR(renv)
	, _peer(peer)
	, _peerId(_peer->_id.address().toInt())
	, _qosCutoffCount(0)
	, _ackCutoffCount(0)
	, _lastSummaryDump(0)
	, _lastAckRateCheck(0)
	, _lastQoSRateCheck(0)
	, _lastQualityEstimation(0)
	, _lastCheckUserPreferences(0)
	, _lastBackgroundTaskCheck(0)
	, _lastBondStatusLog(0)
	, _lastPathNegotiationReceived(0)
	, _lastPathNegotiationCheck(0)
	, _lastSentPathNegotiationRequest(0)
	, _lastFlowStatReset(0)
	, _lastFlowExpirationCheck(0)
	, _lastFlowRebalance(0)
	, _lastFrame(0)
	, _lastActiveBackupPathChange(0)
{
	setReasonableDefaults(policy, SharedPtr<Bond>(), false);
	_policyAlias = BondController::getPolicyStrByCode(policy);
}

Bond::Bond(const RuntimeEnvironment* renv, std::string& basePolicy, std::string& policyAlias, const SharedPtr<Peer>& peer) : RR(renv), _policyAlias(policyAlias), _peer(peer)
{
	setReasonableDefaults(BondController::getPolicyCodeByStr(basePolicy), SharedPtr<Bond>(), false);
}

Bond::Bond(const RuntimeEnvironment* renv, SharedPtr<Bond> originalBond, const SharedPtr<Peer>& peer)
	: RR(renv)
	, _peer(peer)
	, _peerId(_peer->_id.address().toInt())
	, _lastAckRateCheck(0)
	, _lastQoSRateCheck(0)
	, _lastQualityEstimation(0)
	, _lastCheckUserPreferences(0)
	, _lastBackgroundTaskCheck(0)
	, _lastBondStatusLog(0)
	, _lastPathNegotiationReceived(0)
	, _lastPathNegotiationCheck(0)
	, _lastFlowStatReset(0)
	, _lastFlowExpirationCheck(0)
	, _lastFlowRebalance(0)
	, _lastFrame(0)
{
	setReasonableDefaults(originalBond->_bondingPolicy, originalBond, true);
}

void Bond::nominatePath(const SharedPtr<Path>& path, int64_t now)
{
	char pathStr[64] = { 0 };
	path->address().toString(pathStr);
	Mutex::Lock _l(_paths_m);
	if (! RR->bc->linkAllowed(_policyAlias, getLink(path))) {
		return;
	}
	bool alreadyPresent = false;
	for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (path.ptr() == _paths[i].ptr()) {
			// Previously encountered path, not notifying bond
			alreadyPresent = true;
			break;
		}
	}
	if (! alreadyPresent) {
		for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
			if (! _paths[i]) {
				_paths[i] = path;
				_paths[i]->startTrial(now);
				log("bond", "nominate link %s/%s (now in trial period)", getLink(path)->ifname().c_str(), pathStr);
				break;
			}
		}
	}
	curateBond(now, true);
	estimatePathQuality(now);
}

SharedPtr<Path> Bond::getAppropriatePath(int64_t now, int32_t flowId)
{
	Mutex::Lock _l(_paths_m);
	/**
	 * active-backup
	 */
	if (_bondingPolicy == ZT_BONDING_POLICY_ACTIVE_BACKUP) {
		if (_abPath) {
			return _abPath;
		}
	}
	/**
	 * broadcast
	 */
	if (_bondingPolicy == ZT_BONDING_POLICY_BROADCAST) {
		return SharedPtr<Path>();	// Handled in Switch::_trySend()
	}
	if (! _numBondedPaths) {
		return SharedPtr<Path>();	// No paths assigned to bond yet, cannot balance traffic
	}
	/**
	 * balance-rr
	 */
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_RR) {
		if (! _allowFlowHashing) {
			if (_packetsPerLink == 0) {
				// Randomly select a path
				return _paths[_bondedIdx[_freeRandomByte % _numBondedPaths]];	// TODO: Optimize
			}
			if (_rrPacketsSentOnCurrLink < _packetsPerLink) {
				// Continue to use this link
				++_rrPacketsSentOnCurrLink;
				return _paths[_bondedIdx[_rrIdx]];
			}
			// Reset striping counter
			_rrPacketsSentOnCurrLink = 0;
			if (_numBondedPaths == 1) {
				_rrIdx = 0;
			}
			else {
				int _tempIdx = _rrIdx;
				for (int searchCount = 0; searchCount < (_numBondedPaths - 1); searchCount++) {
					_tempIdx = (_tempIdx == (_numBondedPaths - 1)) ? 0 : _tempIdx + 1;
					if (_bondedIdx[_tempIdx] != ZT_MAX_PEER_NETWORK_PATHS) {
						if (_paths[_bondedIdx[_tempIdx]] && _paths[_bondedIdx[_tempIdx]]->eligible(now, _ackSendInterval)) {
							_rrIdx = _tempIdx;
							break;
						}
					}
				}
			}
			if (_paths[_bondedIdx[_rrIdx]]) {
				return _paths[_bondedIdx[_rrIdx]];
			}
		}
	}
	/**
	 * balance-xor
	 */
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_XOR || _bondingPolicy == ZT_BONDING_POLICY_BALANCE_AWARE) {
		if (! _allowFlowHashing || flowId == -1) {
			// No specific path required for unclassified traffic, send on anything
			return _paths[_bondedIdx[_freeRandomByte % _numBondedPaths]];	// TODO: Optimize
		}
		else if (_allowFlowHashing) {
			// TODO: Optimize
			Mutex::Lock _l(_flows_m);
			SharedPtr<Flow> flow;
			if (_flows.count(flowId)) {
				flow = _flows[flowId];
				flow->updateActivity(now);
			}
			else {
				unsigned char entropy;
				Utils::getSecureRandom(&entropy, 1);
				flow = createFlow(SharedPtr<Path>(), flowId, entropy, now);
			}
			if (flow) {
				return flow->assignedPath();
			}
		}
	}
	return SharedPtr<Path>();
}

void Bond::recordIncomingInvalidPacket(const SharedPtr<Path>& path)
{
	// char pathStr[64] = { 0 }; path->address().toString(pathStr);
	// log("bond", "%s (qos) Invalid packet on link %s/%s from peer %llx",
	//	 getLink(path)->ifname().c_str(), pathStr);
	Mutex::Lock _l(_paths_m);
	for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (_paths[i] == path) {
			_paths[i]->packetValiditySamples.push(false);
		}
	}
}

void Bond::recordOutgoingPacket(const SharedPtr<Path>& path, const uint64_t packetId, uint16_t payloadLength, const Packet::Verb verb, const int32_t flowId, int64_t now)
{
	// char pathStr[64] = { 0 }; path->address().toString(pathStr);
	// log("bond", " Outgoing packet on link %s/%s",
	//	 getLink(path)->ifname().c_str(), pathStr);
	_freeRandomByte += (unsigned char)(packetId >> 8);	 // Grab entropy to use in path selection logic
	if (! _shouldCollectPathStatistics) {
		return;
	}
	bool isFrame = (verb == Packet::VERB_FRAME || verb == Packet::VERB_EXT_FRAME);
	bool shouldRecord = (packetId & (ZT_QOS_ACK_DIVISOR - 1) && (verb != Packet::VERB_ACK) && (verb != Packet::VERB_QOS_MEASUREMENT));
	if (isFrame || shouldRecord) {
		Mutex::Lock _l(_paths_m);
		if (isFrame) {
			++(path->_packetsOut);
			_lastFrame = now;
		}
		if (shouldRecord) {
			path->_unackedBytes += payloadLength;
			// Take note that we're expecting a VERB_ACK on this path as of a specific time
			if (path->qosStatsOut.size() < ZT_QOS_MAX_OUTSTANDING_RECORDS) {
				path->qosStatsOut[packetId] = now;
			}
		}
	}
	if (_allowFlowHashing && (flowId != ZT_QOS_NO_FLOW)) {
		Mutex::Lock _l(_flows_m);
		if (_flows.count(flowId)) {
			_flows[flowId]->recordOutgoingBytes(payloadLength);
		}
	}
}

void Bond::recordIncomingPacket(const SharedPtr<Path>& path, uint64_t packetId, uint16_t payloadLength, Packet::Verb verb, int32_t flowId, int64_t now)
{
	// char pathStr[64] = { 0 }; path->address().toString(pathStr);
	// log("bond", " Incoming packet on link %s/%s (ls=%llx) from peer %llx [id=%llx, len=%d, verb=%d, flowId=%x]",
	//	 getLink(path)->ifname().c_str(), pathStr, path->localSocket(), packetId, payloadLength, verb, flowId);
	bool isFrame = (verb == Packet::VERB_FRAME || verb == Packet::VERB_EXT_FRAME);
	bool shouldRecord = (packetId & (ZT_QOS_ACK_DIVISOR - 1) && (verb != Packet::VERB_ACK) && (verb != Packet::VERB_QOS_MEASUREMENT));
	if (isFrame || shouldRecord) {
		Mutex::Lock _l(_paths_m);
		if (path->bonded()) {
			if (isFrame) {
				++(path->_packetsIn);
				_lastFrame = now;
			}
			if (shouldRecord) {
				path->ackStatsIn[packetId] = payloadLength;
				++(path->_packetsReceivedSinceLastAck);
				path->qosStatsIn[packetId] = now;
				++(path->_packetsReceivedSinceLastQoS);
				path->packetValiditySamples.push(true);
			}
		}
	}

	/**
	 * Learn new flows and pro-actively create entries for them in the bond so
	 * that the next time we send a packet out that is part of a flow we know
	 * which path to use.
	 */
	if ((flowId != ZT_QOS_NO_FLOW) && (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_RR || _bondingPolicy == ZT_BONDING_POLICY_BALANCE_XOR || _bondingPolicy == ZT_BONDING_POLICY_BALANCE_AWARE)) {
		Mutex::Lock _l(_flows_m);
		SharedPtr<Flow> flow;
		if (! _flows.count(flowId)) {
			flow = createFlow(path, flowId, 0, now);
		}
		else {
			flow = _flows[flowId];
		}
		if (flow) {
			flow->recordIncomingBytes(payloadLength);
		}
	}
}

void Bond::receivedQoS(const SharedPtr<Path>& path, int64_t now, int count, uint64_t* rx_id, uint16_t* rx_ts)
{
	Mutex::Lock _l(_paths_m);
	// char pathStr[64] = { 0 }; path->address().toString(pathStr);
	// log("bond", "%s (qos) Received QoS packet sampling %d frames from peer %llx via %s/%s",
	//	 count, getLink(path)->ifname().c_str(), pathStr);
	// Look up egress times and compute latency values for each record
	std::map<uint64_t, uint64_t>::iterator it;
	for (int j = 0; j < count; j++) {
		it = path->qosStatsOut.find(rx_id[j]);
		if (it != path->qosStatsOut.end()) {
			path->latencySamples.push(((uint16_t)(now - it->second) - rx_ts[j]) / 2);
			path->qosStatsOut.erase(it);
		}
	}
	path->qosRecordSize.push(count);
}

void Bond::receivedAck(const SharedPtr<Path>& path, int64_t now, int32_t ackedBytes)
{
	Mutex::Lock _l(_paths_m);
	// char pathStr[64] = { 0 }; path->address().toString(pathStr);
	// log("bond", "%s (qos) Received ACK packet for %d bytes from peer %llx via %s/%s",
	//	 ackedBytes, getLink(path)->ifname().c_str(), pathStr);
	path->_lastAckReceived = now;
	path->_unackedBytes = (ackedBytes > path->_unackedBytes) ? 0 : path->_unackedBytes - ackedBytes;
	int64_t timeSinceThroughputEstimate = (now - path->_lastThroughputEstimation);
	if (timeSinceThroughputEstimate >= throughputMeasurementInterval) {
		// TODO: See if this floating point math can be reduced
		uint64_t throughput = (uint64_t)((float)(path->_bytesAckedSinceLastThroughputEstimation) / ((float)timeSinceThroughputEstimate / (float)1000));
		throughput /= 1000;
		if (throughput > 0.0) {
			path->throughputSamples.push(throughput);
			path->_throughputMax = throughput > path->_throughputMax ? throughput : path->_throughputMax;
		}
		path->_lastThroughputEstimation = now;
		path->_bytesAckedSinceLastThroughputEstimation = 0;
	}
	else {
		path->_bytesAckedSinceLastThroughputEstimation += ackedBytes;
	}
}

int32_t Bond::generateQoSPacket(const SharedPtr<Path>& path, int64_t now, char* qosBuffer)
{
	int32_t len = 0;
	std::map<uint64_t, uint64_t>::iterator it = path->qosStatsIn.begin();
	int i = 0;
	int numRecords = std::min(path->_packetsReceivedSinceLastQoS, ZT_QOS_TABLE_SIZE);
	while (i < numRecords && it != path->qosStatsIn.end()) {
		uint64_t id = it->first;
		memcpy(qosBuffer, &id, sizeof(uint64_t));
		qosBuffer += sizeof(uint64_t);
		uint16_t holdingTime = (uint16_t)(now - it->second);
		memcpy(qosBuffer, &holdingTime, sizeof(uint16_t));
		qosBuffer += sizeof(uint16_t);
		len += sizeof(uint64_t) + sizeof(uint16_t);
		path->qosStatsIn.erase(it++);
		++i;
	}
	return len;
}

bool Bond::assignFlowToBondedPath(SharedPtr<Flow>& flow, int64_t now)
{
	char curPathStr[64] = { 0 };
	unsigned int idx = ZT_MAX_PEER_NETWORK_PATHS;
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_XOR) {
		idx = abs((int)(flow->id() % (_numBondedPaths)));
		SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[_bondedIdx[idx]]->localSocket());
		_paths[_bondedIdx[idx]]->address().toString(curPathStr);
		log("xor", "assign out-flow %x to link %s/%s (total flows: %lu)", flow->id(), link->ifname().c_str(), curPathStr, (unsigned long)_flows.size());
		flow->assignPath(_paths[_bondedIdx[idx]], now);
		++(_paths[_bondedIdx[idx]]->_assignedFlowCount);
	}
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_AWARE) {
		unsigned char entropy;
		Utils::getSecureRandom(&entropy, 1);
		if (_totalBondUnderload) {
			entropy %= _totalBondUnderload;
		}
		if (! _numBondedPaths) {
			log("aware", "unable to assign flow %x (bond has no links)\n", flow->id());
			return false;
		}
		/* Since there may be scenarios where a path is removed before we can re-estimate
		relative qualities (and thus allocations) we need to down-modulate the entropy
		value that we use to randomly assign among the surviving paths, otherwise we risk
		not being able to find a path to assign this flow to. */
		int totalIncompleteAllocation = 0;
		for (unsigned int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
			if (_paths[i] && _paths[i]->bonded()) {
				totalIncompleteAllocation += _paths[i]->_allocation;
			}
		}
		entropy %= totalIncompleteAllocation;
		for (unsigned int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
			if (_paths[i] && _paths[i]->bonded()) {
				SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
				_paths[i]->address().toString(curPathStr);
				uint8_t probabilitySegment = (_totalBondUnderload > 0) ? _paths[i]->_affinity : _paths[i]->_allocation;
				if (entropy <= probabilitySegment) {
					idx = i;
					break;
				}
				entropy -= probabilitySegment;
			}
		}
		if (idx < ZT_MAX_PEER_NETWORK_PATHS) {
			if (flow->_assignedPath) {
				flow->_previouslyAssignedPath = flow->_assignedPath;
			}
			flow->assignPath(_paths[idx], now);
			++(_paths[idx]->_assignedFlowCount);
		}
		else {
			log("aware", "unable to assign out-flow %x (unknown reason)", flow->id());
			return false;
		}
	}
	if (_bondingPolicy == ZT_BONDING_POLICY_ACTIVE_BACKUP) {
		if (_abOverflowEnabled) {
			flow->assignPath(_abPath, now);
		}
		else {
			log("aware", "unable to assign out-flow %x (no active overflow link)", flow->id());
			return false;
		}
	}
	flow->assignedPath()->address().toString(curPathStr);
	SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, flow->assignedPath()->localSocket());
	log("bond", "assign out-flow %x to link %s/%s (total flows: %lu)", flow->id(), link->ifname().c_str(), curPathStr, (unsigned long)_flows.size());
	return true;
}

SharedPtr<Flow> Bond::createFlow(const SharedPtr<Path>& path, int32_t flowId, unsigned char entropy, int64_t now)
{
	char curPathStr[64] = { 0 };
	// ---
	if (! _numBondedPaths) {
		log("bond", "unable to assign flow %x (bond has no links)\n", flowId);
		return SharedPtr<Flow>();
	}
	if (_flows.size() >= ZT_FLOW_MAX_COUNT) {
		log("bond", "forget oldest flow (max flows reached: %d)\n", ZT_FLOW_MAX_COUNT);
		forgetFlowsWhenNecessary(0, true, now);
	}
	SharedPtr<Flow> flow = new Flow(flowId, now);
	_flows[flowId] = flow;
	/**
	 * Add a flow with a given Path already provided. This is the case when a packet
	 * is received on a path but no flow exists, in this case we simply assign the path
	 * that the remote peer chose for us.
	 */
	if (path) {
		flow->assignPath(path, now);
		path->address().toString(curPathStr);
		path->_assignedFlowCount++;
		SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, flow->assignedPath()->localSocket());
		log("bond", "assign in-flow %x to link %s/%s (total flows: %lu)", flow->id(), link->ifname().c_str(), curPathStr, (unsigned long)_flows.size());
	}
	/**
	 * Add a flow when no path was provided. This means that it is an outgoing packet
	 * and that it is up to the local peer to decide how to load-balance its transmission.
	 */
	else if (! path) {
		assignFlowToBondedPath(flow, now);
	}
	return flow;
}

void Bond::forgetFlowsWhenNecessary(uint64_t age, bool oldest, int64_t now)
{
	std::map<int32_t, SharedPtr<Flow> >::iterator it = _flows.begin();
	std::map<int32_t, SharedPtr<Flow> >::iterator oldestFlow = _flows.end();
	SharedPtr<Flow> expiredFlow;
	if (age) {	 // Remove by specific age
		while (it != _flows.end()) {
			if (it->second->age(now) > age) {
				log("bond", "forget flow %x (age %llu) (total flows: %lu)", it->first, (unsigned long long)oldestFlow->second->age(now), (unsigned long)(_flows.size() - 1));
				it->second->assignedPath()->_assignedFlowCount--;
				it = _flows.erase(it);
			}
			else {
				++it;
			}
		}
	}
	else if (oldest) {	 // Remove single oldest by natural expiration
		uint64_t maxAge = 0;
		while (it != _flows.end()) {
			if (it->second->age(now) > maxAge) {
				maxAge = (now - it->second->age(now));
				oldestFlow = it;
			}
			++it;
		}
		if (oldestFlow != _flows.end()) {
			log("bond", "forget oldest flow %x (age %llu) (total flows: %lu)", oldestFlow->first, (unsigned long long)oldestFlow->second->age(now), (unsigned long)(_flows.size() - 1));
			oldestFlow->second->assignedPath()->_assignedFlowCount--;
			_flows.erase(oldestFlow);
		}
	}
}

void Bond::processIncomingPathNegotiationRequest(uint64_t now, SharedPtr<Path>& path, int16_t remoteUtility)
{
	char pathStr[64] = { 0 };
	if (_abLinkSelectMethod != ZT_MULTIPATH_RESELECTION_POLICY_OPTIMIZE) {
		return;
	}
	Mutex::Lock _l(_paths_m);
	path->address().toString(pathStr);
	if (! _lastPathNegotiationCheck) {
		return;
	}
	SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, path->localSocket());
	if (remoteUtility > _localUtility) {
		path->address().toString(pathStr);
		log("bond", "peer suggests alternate link %s/%s, remote utility (%d) greater than local utility (%d), switching to suggested link\n", link->ifname().c_str(), pathStr, remoteUtility, _localUtility);
		negotiatedPath = path;
	}
	if (remoteUtility < _localUtility) {
		log("bond", "peer suggests alternate link %s/%s, remote utility (%d) less than local utility (%d), not switching\n", link->ifname().c_str(), pathStr, remoteUtility, _localUtility);
	}
	if (remoteUtility == _localUtility) {
		log("bond", "peer suggests alternate link %s/%s, remote utility (%d) equal to local utility (%d)\n", link->ifname().c_str(), pathStr, remoteUtility, _localUtility);
		if (_peer->_id.address().toInt() > RR->node->identity().address().toInt()) {
			log("bond", "agree with peer to use alternate link %s/%s\n", link->ifname().c_str(), pathStr);
			negotiatedPath = path;
		}
		else {
			log("bond", "ignore petition from peer to use alternate link %s/%s\n", link->ifname().c_str(), pathStr);
		}
	}
}

void Bond::pathNegotiationCheck(void* tPtr, const int64_t now)
{
	char pathStr[64] = { 0 };
	int maxInPathIdx = ZT_MAX_PEER_NETWORK_PATHS;
	int maxOutPathIdx = ZT_MAX_PEER_NETWORK_PATHS;
	uint64_t maxInCount = 0;
	uint64_t maxOutCount = 0;
	for (unsigned int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (! _paths[i]) {
			continue;
		}
		if (_paths[i]->_packetsIn > maxInCount) {
			maxInCount = _paths[i]->_packetsIn;
			maxInPathIdx = i;
		}
		if (_paths[i]->_packetsOut > maxOutCount) {
			maxOutCount = _paths[i]->_packetsOut;
			maxOutPathIdx = i;
		}
		_paths[i]->resetPacketCounts();
	}
	bool _peerLinksSynchronized = ((maxInPathIdx != ZT_MAX_PEER_NETWORK_PATHS) && (maxOutPathIdx != ZT_MAX_PEER_NETWORK_PATHS) && (maxInPathIdx != maxOutPathIdx)) ? false : true;
	/**
	 * Determine utility and attempt to petition remote peer to switch to our chosen path
	 */
	if (! _peerLinksSynchronized) {
		_localUtility = _paths[maxOutPathIdx]->_failoverScore - _paths[maxInPathIdx]->_failoverScore;
		if (_paths[maxOutPathIdx]->_negotiated) {
			_localUtility -= ZT_MULTIPATH_FAILOVER_HANDICAP_NEGOTIATED;
		}
		if ((now - _lastSentPathNegotiationRequest) > ZT_PATH_NEGOTIATION_CUTOFF_TIME) {
			// fprintf(stderr, "BT: (sync) it's been long enough, sending more requests.\n");
			_numSentPathNegotiationRequests = 0;
		}
		if (_numSentPathNegotiationRequests < ZT_PATH_NEGOTIATION_TRY_COUNT) {
			if (_localUtility >= 0) {
				// fprintf(stderr, "BT: (sync) paths appear to be out of sync (utility=%d)\n", _localUtility);
				sendPATH_NEGOTIATION_REQUEST(tPtr, _paths[maxOutPathIdx]);
				++_numSentPathNegotiationRequests;
				_lastSentPathNegotiationRequest = now;
				_paths[maxOutPathIdx]->address().toString(pathStr);
				SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[maxOutPathIdx]->localSocket());
				// fprintf(stderr, "sending request to use %s on %s, ls=%llx, utility=%d\n", pathStr, link->ifname().c_str(), _paths[maxOutPathIdx]->localSocket(), _localUtility);
			}
		}
		/**
		 * Give up negotiating and consider switching
		 */
		else if ((now - _lastSentPathNegotiationRequest) > (2 * ZT_PATH_NEGOTIATION_CHECK_INTERVAL)) {
			if (_localUtility == 0) {
				// There's no loss to us, just switch without sending a another request
				// fprintf(stderr, "BT: (sync) giving up, switching to remote peer's path.\n");
				negotiatedPath = _paths[maxInPathIdx];
			}
		}
	}
}

void Bond::sendPATH_NEGOTIATION_REQUEST(void* tPtr, const SharedPtr<Path>& path)
{
	char pathStr[64] = { 0 };
	path->address().toString(pathStr);
	log("bond", "send link negotiation request to peer via link %s/%s, local utility is %d", getLink(path)->ifname().c_str(), pathStr, _localUtility);
	if (_abLinkSelectMethod != ZT_MULTIPATH_RESELECTION_POLICY_OPTIMIZE) {
		return;
	}
	Packet outp(_peer->_id.address(), RR->identity.address(), Packet::VERB_PATH_NEGOTIATION_REQUEST);
	outp.append<int16_t>(_localUtility);
	if (path->address()) {
		outp.armor(_peer->key(), false, _peer->aesKeysIfSupported());
		RR->node->putPacket(tPtr, path->localSocket(), path->address(), outp.data(), outp.size());
	}
}

void Bond::sendACK(void* tPtr, const SharedPtr<Path>& path, const int64_t localSocket, const InetAddress& atAddress, int64_t now)
{
	Packet outp(_peer->_id.address(), RR->identity.address(), Packet::VERB_ACK);
	int32_t bytesToAck = 0;
	std::map<uint64_t, uint16_t>::iterator it = path->ackStatsIn.begin();
	while (it != path->ackStatsIn.end()) {
		bytesToAck += it->second;
		++it;
	}
	// char pathStr[64] = { 0 }; path->address().toString(pathStr);
	// log("bond", "%s (qos) Sending ACK packet for %d bytes via link %s/%s",
	//	 bytesToAck, getLink(path)->ifname().c_str(), pathStr);
	outp.append<uint32_t>(bytesToAck);
	if (atAddress) {
		outp.armor(_peer->key(), false, _peer->aesKeysIfSupported());
		RR->node->putPacket(tPtr, localSocket, atAddress, outp.data(), outp.size());
	}
	else {
		RR->sw->send(tPtr, outp, false);
	}
	path->ackStatsIn.clear();
	path->_packetsReceivedSinceLastAck = 0;
	path->_lastAckSent = now;
}

void Bond::sendQOS_MEASUREMENT(void* tPtr, const SharedPtr<Path>& path, const int64_t localSocket, const InetAddress& atAddress, int64_t now)
{
	// char pathStr[64] = { 0 }; path->address().toString(pathStr);
	// log("bond", "%s (qos) Sending QoS packet via link %s/%s",
	//	 _peerId, getLink(path)->ifname().c_str(), pathStr);
	const int64_t _now = RR->node->now();
	Packet outp(_peer->_id.address(), RR->identity.address(), Packet::VERB_QOS_MEASUREMENT);
	char qosData[ZT_QOS_MAX_PACKET_SIZE];
	int16_t len = generateQoSPacket(path, _now, qosData);
	outp.append(qosData, len);
	if (atAddress) {
		outp.armor(_peer->key(), false, _peer->aesKeysIfSupported());
		RR->node->putPacket(tPtr, localSocket, atAddress, outp.data(), outp.size());
	}
	else {
		RR->sw->send(tPtr, outp, false);
	}
	// Account for the fact that a VERB_QOS_MEASUREMENT was just sent. Reset timers.
	path->_packetsReceivedSinceLastQoS = 0;
	path->_lastQoSMeasurement = now;
}

void Bond::processBackgroundTasks(void* tPtr, const int64_t now)
{
	Mutex::Lock _l(_paths_m);
	if (! _peer->_canUseMultipath || (now - _lastBackgroundTaskCheck) < ZT_BOND_BACKGROUND_TASK_MIN_INTERVAL) {
		return;
	}
	_lastBackgroundTaskCheck = now;

	// Compute dynamic path monitor timer interval
	if (_linkMonitorStrategy == ZT_MULTIPATH_SLAVE_MONITOR_STRATEGY_DYNAMIC) {
		int suggestedMonitorInterval = (now - _lastFrame) / 100;
		_dynamicPathMonitorInterval = std::min(ZT_PATH_HEARTBEAT_PERIOD, ((suggestedMonitorInterval > _bondMonitorInterval) ? suggestedMonitorInterval : _bondMonitorInterval));
	}
	// TODO: Clarify and generalize this logic
	if (_linkMonitorStrategy == ZT_MULTIPATH_SLAVE_MONITOR_STRATEGY_DYNAMIC) {
		_shouldCollectPathStatistics = true;
	}

	// Memoize oft-used properties in the packet ingress/egress logic path
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_AWARE) {
		// Required for real-time balancing
		_shouldCollectPathStatistics = true;
	}
	if (_bondingPolicy == ZT_BONDING_POLICY_ACTIVE_BACKUP) {
		if (_abLinkSelectMethod == ZT_MULTIPATH_RESELECTION_POLICY_BETTER) {
			// Required for judging suitability of primary link after recovery
			_shouldCollectPathStatistics = true;
		}
		if (_abLinkSelectMethod == ZT_MULTIPATH_RESELECTION_POLICY_OPTIMIZE) {
			// Required for judging suitability of new candidate primary
			_shouldCollectPathStatistics = true;
		}
	}
	if ((now - _lastCheckUserPreferences) > 1000) {
		_lastCheckUserPreferences = now;
		applyUserPrefs();
	}

	curateBond(now, false);
	if ((now - _lastQualityEstimation) > _qualityEstimationInterval) {
		_lastQualityEstimation = now;
		estimatePathQuality(now);
	}
	dumpInfo(now, false);

	// Send QOS/ACK packets as needed
	if (_shouldCollectPathStatistics) {
		for (unsigned int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
			if (_paths[i] && _paths[i]->allowed()) {
				if (_paths[i]->needsToSendQoS(now, _qosSendInterval)) {
					sendQOS_MEASUREMENT(tPtr, _paths[i], _paths[i]->localSocket(), _paths[i]->address(), now);
				}
				if (_paths[i]->needsToSendAck(now, _ackSendInterval)) {
					sendACK(tPtr, _paths[i], _paths[i]->localSocket(), _paths[i]->address(), now);
				}
			}
		}
	}
	// Perform periodic background tasks unique to each bonding policy
	switch (_bondingPolicy) {
		case ZT_BONDING_POLICY_ACTIVE_BACKUP:
			processActiveBackupTasks(tPtr, now);
			break;
		case ZT_BONDING_POLICY_BROADCAST:
			break;
		case ZT_BONDING_POLICY_BALANCE_RR:
		case ZT_BONDING_POLICY_BALANCE_XOR:
		case ZT_BONDING_POLICY_BALANCE_AWARE:
			processBalanceTasks(now);
			break;
		default:
			break;
	}
	// Check whether or not a path negotiation needs to be performed
	if (((now - _lastPathNegotiationCheck) > ZT_PATH_NEGOTIATION_CHECK_INTERVAL) && _allowPathNegotiation) {
		_lastPathNegotiationCheck = now;
		pathNegotiationCheck(tPtr, now);
	}
}

void Bond::applyUserPrefs()
{
	for (unsigned int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (! _paths[i]) {
			continue;
		}
		SharedPtr<Link> sl = getLink(_paths[i]);
		if (sl) {
			if (sl->monitorInterval() == 0) {	// If no interval was specified for this link, use more generic bond-wide interval
				sl->setMonitorInterval(_bondMonitorInterval);
			}
			RR->bc->setMinReqPathMonitorInterval((sl->monitorInterval() < RR->bc->minReqPathMonitorInterval()) ? sl->monitorInterval() : RR->bc->minReqPathMonitorInterval());
			bool bFoundCommonLink = false;
			SharedPtr<Link> commonLink = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
			for (unsigned int j = 0; j < ZT_MAX_PEER_NETWORK_PATHS; ++j) {
				if (_paths[j] && _paths[j].ptr() != _paths[i].ptr()) {
					if (RR->bc->getLinkBySocket(_policyAlias, _paths[j]->localSocket()) == commonLink) {
						bFoundCommonLink = true;
					}
				}
			}
			_paths[i]->_monitorInterval = sl->monitorInterval();
			_paths[i]->_upDelay = sl->upDelay() ? sl->upDelay() : _upDelay;
			_paths[i]->_downDelay = sl->downDelay() ? sl->downDelay() : _downDelay;
			_paths[i]->_ipvPref = sl->ipvPref();
			_paths[i]->_mode = sl->mode();
			_paths[i]->_enabled = sl->enabled();
			_paths[i]->_onlyPathOnLink = ! bFoundCommonLink;
		}
	}
	if (_peer) {
		_peer->_shouldCollectPathStatistics = _shouldCollectPathStatistics;
		_peer->_bondingPolicy = _bondingPolicy;
	}
}

void Bond::curateBond(const int64_t now, bool rebuildBond)
{
	char pathStr[64] = { 0 };
	uint8_t tmpNumAliveLinks = 0;
	uint8_t tmpNumTotalLinks = 0;
	/**
	 * Update path states
	 */
	for (unsigned int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (! _paths[i]) {
			continue;
		}
		tmpNumTotalLinks++;
		if (_paths[i]->alive(now, true)) {
			tmpNumAliveLinks++;
		}
		bool currEligibility = _paths[i]->eligible(now, _ackSendInterval);
		if (currEligibility != _paths[i]->_lastEligibilityState) {
			_paths[i]->address().toString(pathStr);
			if (currEligibility == 0) {
				log("bond", "link %s/%s is no longer eligible", getLink(_paths[i])->ifname().c_str(), pathStr);
			}
			if (currEligibility == 1) {
				log("bond", "link %s/%s is eligible", getLink(_paths[i])->ifname().c_str(), pathStr);
			}
			dumpPathStatus(now, _paths[i], i);
			if (currEligibility) {
				rebuildBond = true;
			}
			if (! currEligibility) {
				_paths[i]->adjustRefractoryPeriod(now, _defaultPathRefractoryPeriod, ! currEligibility);
				if (_paths[i]->bonded()) {
					_paths[i]->address().toString(pathStr);
					log("bond", "link %s/%s was bonded, flow reallocation will occur soon", getLink(_paths[i])->ifname().c_str(), pathStr);
					rebuildBond = true;
					_paths[i]->_shouldReallocateFlows = _paths[i]->bonded();
					_paths[i]->setBonded(false);
				}
				else {
					log("bond", "link %s/%s was not bonded, no allocation consequences", getLink(_paths[i])->ifname().c_str(), pathStr);
				}
			}
		}
		if (currEligibility) {
			_paths[i]->adjustRefractoryPeriod(now, _defaultPathRefractoryPeriod, false);
		}
		_paths[i]->_lastEligibilityState = currEligibility;
	}
	_numAliveLinks = tmpNumAliveLinks;
	_numTotalLinks = tmpNumTotalLinks;

	/* Determine health status to report to user */

	bool tmpHealthStatus = true;

	if (_bondingPolicy == ZT_BONDING_POLICY_ACTIVE_BACKUP) {
		if (_numAliveLinks < 2) {
			// Considered healthy if there is at least one failover link
			tmpHealthStatus = false;
		}
	}
	if (_bondingPolicy == ZT_BONDING_POLICY_BROADCAST) {
		if (_numAliveLinks < 1) {
			// Considered healthy if we're able to send frames at all
			tmpHealthStatus = false;
		}
	}
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_RR) {
		if (_numAliveLinks < _numTotalLinks) {
			// Considered healthy if all known paths are alive, this should be refined to account for user bond config settings
			tmpHealthStatus = false;
		}
	}
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_XOR) {
		if (_numAliveLinks < _numTotalLinks) {
			// Considered healthy if all known paths are alive, this should be refined to account for user bond config settings
			tmpHealthStatus = false;
		}
	}
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_AWARE) {
		if (_numAliveLinks < _numTotalLinks) {
			// Considered healthy if all known paths are alive, this should be refined to account for user bond config settings
			tmpHealthStatus = false;
		}
	}
	if (tmpHealthStatus != _isHealthy) {
		std::string healthStatusStr;
		if (tmpHealthStatus == true) {
			healthStatusStr = "HEALTHY";
		}
		else {
			healthStatusStr = "DEGRADED";
		}
		log("bond", "bond is in a %s state (links: %d/%d)", healthStatusStr.c_str(), _numAliveLinks, _numTotalLinks);
		dumpInfo(now, true);
	}

	_isHealthy = tmpHealthStatus;

	/**
	 * Curate the set of paths that are part of the bond proper. Select a set of paths
	 * per logical link according to eligibility and user-specified constraints.
	 */
	if ((_bondingPolicy == ZT_BONDING_POLICY_BALANCE_RR) || (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_XOR) || (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_AWARE)) {
		if (! _numBondedPaths) {
			rebuildBond = true;
		}
		if (rebuildBond) {
			log("bond", "rebuilding bond");
			// TODO: Obey blacklisting
			int updatedBondedPathCount = 0;
			// Build map associating paths with local physical links. Will be selected from in next step
			std::map<SharedPtr<Link>, std::vector<int> > linkMap;
			for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
				if (_paths[i]) {
					SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
					if (! linkMap.count(link)) {
						// linkMap[link] = std::vector<int>(i);
					}
					linkMap[link].push_back(i);
				}
			}
			// Re-form bond from link<->path map
			std::map<SharedPtr<Link>, std::vector<int> >::iterator it = linkMap.begin();
			while (it != linkMap.end()) {
				SharedPtr<Link> link = it->first;
				int ipvPref = link->ipvPref();

				// If user has no address type preference, then use every path we find on a link
				if (ipvPref == 0) {
					for (int j = 0; j < it->second.size(); j++) {
						int idx = it->second.at(j);
						if (! _paths[idx] || ! _paths[idx]->allowed()) {
							continue;
						}
						_bondedIdx[updatedBondedPathCount] = idx;
						_paths[idx]->setBonded(true);
						++updatedBondedPathCount;
						_paths[idx]->address().toString(pathStr);
						log("bond", "add %s/%s (no user addr preference)", link->ifname().c_str(), pathStr);
					}
				}
				// If the user prefers to only use one address type (IPv4 or IPv6)
				if (ipvPref == 4 || ipvPref == 6) {
					for (int j = 0; j < it->second.size(); j++) {
						int idx = it->second.at(j);
						if (! _paths[idx]) {
							continue;
						}
						if (! _paths[idx]->allowed()) {
							_paths[idx]->address().toString(pathStr);
							log("bond", "did not add %s/%s (user addr preference %d)", link->ifname().c_str(), pathStr, ipvPref);
							continue;
						}
						if (! _paths[idx]->eligible(now, _ackSendInterval)) {
							continue;
						}
						_bondedIdx[updatedBondedPathCount] = idx;
						_paths[idx]->setBonded(true);
						++updatedBondedPathCount;
						_paths[idx]->address().toString(pathStr);
						log("bond", "add path %s/%s (user addr preference %d)", link->ifname().c_str(), pathStr, ipvPref);
					}
				}
				// If the users prefers one address type to another, try to find at least
				// one path of that type before considering others.
				if (ipvPref == 46 || ipvPref == 64) {
					bool foundPreferredPath = false;
					// Search for preferred paths
					for (int j = 0; j < it->second.size(); j++) {
						int idx = it->second.at(j);
						if (! _paths[idx] || ! _paths[idx]->eligible(now, _ackSendInterval)) {
							continue;
						}
						if (_paths[idx]->preferred() && _paths[idx]->allowed()) {
							_bondedIdx[updatedBondedPathCount] = idx;
							_paths[idx]->setBonded(true);
							++updatedBondedPathCount;
							_paths[idx]->address().toString(pathStr);
							log("bond", "add %s/%s (user addr preference %d)", link->ifname().c_str(), pathStr, ipvPref);
							foundPreferredPath = true;
						}
					}
					// Unable to find a path that matches user preference, settle for another address type
					if (! foundPreferredPath) {
						log("bond", "did not find first-choice path type on link %s (user preference %d)", link->ifname().c_str(), ipvPref);
						for (int j = 0; j < it->second.size(); j++) {
							int idx = it->second.at(j);
							if (! _paths[idx] || ! _paths[idx]->eligible(now, _ackSendInterval)) {
								continue;
							}
							_bondedIdx[updatedBondedPathCount] = idx;
							_paths[idx]->setBonded(true);
							++updatedBondedPathCount;
							_paths[idx]->address().toString(pathStr);
							log("bond", "add %s/%s (user addr preference %d)", link->ifname().c_str(), pathStr, ipvPref);
							foundPreferredPath = true;
						}
					}
				}
				++it;	// Next link
			}
			_numBondedPaths = updatedBondedPathCount;
			if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_RR) {
				// Cause a RR reset since the current index might no longer be valid
				_rrPacketsSentOnCurrLink = _packetsPerLink;
			}
		}
	}
}

void Bond::estimatePathQuality(const int64_t now)
{
	uint32_t totUserSpecifiedLinkSpeed = 0;
	if (_numBondedPaths) {	 // Compute relative user-specified speeds of links
		for (unsigned int i = 0; i < _numBondedPaths; ++i) {
			SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
			if (_paths[i] && _paths[i]->allowed()) {
				totUserSpecifiedLinkSpeed += link->speed();
			}
		}
		for (unsigned int i = 0; i < _numBondedPaths; ++i) {
			SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
			if (_paths[i] && _paths[i]->allowed()) {
				link->setRelativeSpeed((uint8_t)round(((float)link->speed() / (float)totUserSpecifiedLinkSpeed) * 255));
			}
		}
	}

	float lat[ZT_MAX_PEER_NETWORK_PATHS] = { 0 };
	float pdv[ZT_MAX_PEER_NETWORK_PATHS] = { 0 };
	float plr[ZT_MAX_PEER_NETWORK_PATHS] = { 0 };
	float per[ZT_MAX_PEER_NETWORK_PATHS] = { 0 };

	float maxLAT = 0;
	float maxPDV = 0;
	float maxPLR = 0;
	float maxPER = 0;

	float quality[ZT_MAX_PEER_NETWORK_PATHS] = { 0 };
	uint8_t alloc[ZT_MAX_PEER_NETWORK_PATHS] = { 0 };

	float totQuality = 0.0f;

	// Compute initial summary statistics
	for (unsigned int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (! _paths[i] || ! _paths[i]->allowed()) {
			continue;
		}
		// Compute/Smooth average of real-world observations
		_paths[i]->_latencyMean = _paths[i]->latencySamples.mean();
		_paths[i]->_latencyVariance = _paths[i]->latencySamples.stddev();
		_paths[i]->_packetErrorRatio = 1.0 - (_paths[i]->packetValiditySamples.count() ? _paths[i]->packetValiditySamples.mean() : 1.0);

		if (userHasSpecifiedLinkSpeeds()) {
			// Use user-reported metrics
			SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
			if (link) {
				_paths[i]->_throughputMean = link->speed();
				_paths[i]->_throughputVariance = 0;
			}
		}
		// Drain unacknowledged QoS records
		std::map<uint64_t, uint64_t>::iterator it = _paths[i]->qosStatsOut.begin();
		uint64_t currentLostRecords = 0;
		while (it != _paths[i]->qosStatsOut.end()) {
			int qosRecordTimeout = 5000;   //_paths[i]->monitorInterval() * ZT_MULTIPATH_QOS_ACK_INTERVAL_MULTIPLIER * 8;
			if ((now - it->second) >= qosRecordTimeout) {
				// Packet was lost
				it = _paths[i]->qosStatsOut.erase(it);
				++currentLostRecords;
			}
			else {
				++it;
			}
		}

		quality[i] = 0;
		totQuality = 0;
		// Normalize raw observations according to sane limits and/or user specified values
		lat[i] = 1.0 / expf(4 * Utils::normalize(_paths[i]->_latencyMean, 0, _maxAcceptableLatency, 0, 1));
		pdv[i] = 1.0 / expf(4 * Utils::normalize(_paths[i]->_latencyVariance, 0, _maxAcceptablePacketDelayVariance, 0, 1));
		plr[i] = 1.0 / expf(4 * Utils::normalize(_paths[i]->_packetLossRatio, 0, _maxAcceptablePacketLossRatio, 0, 1));
		per[i] = 1.0 / expf(4 * Utils::normalize(_paths[i]->_packetErrorRatio, 0, _maxAcceptablePacketErrorRatio, 0, 1));
		// Record bond-wide maximums to determine relative values
		maxLAT = lat[i] > maxLAT ? lat[i] : maxLAT;
		maxPDV = pdv[i] > maxPDV ? pdv[i] : maxPDV;
		maxPLR = plr[i] > maxPLR ? plr[i] : maxPLR;
		maxPER = per[i] > maxPER ? per[i] : maxPER;
	}
	// Convert metrics to relative quantities and apply contribution weights
	for (unsigned int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (_paths[i] && _paths[i]->bonded()) {
			quality[i] += ((maxLAT > 0.0f ? lat[i] / maxLAT : 0.0f) * _qualityWeights[ZT_QOS_LAT_IDX]);
			quality[i] += ((maxPDV > 0.0f ? pdv[i] / maxPDV : 0.0f) * _qualityWeights[ZT_QOS_PDV_IDX]);
			quality[i] += ((maxPLR > 0.0f ? plr[i] / maxPLR : 0.0f) * _qualityWeights[ZT_QOS_PLR_IDX]);
			quality[i] += ((maxPER > 0.0f ? per[i] / maxPER : 0.0f) * _qualityWeights[ZT_QOS_PER_IDX]);
			totQuality += quality[i];
		}
	}
	// Normalize to 8-bit allocation values
	for (unsigned int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (_paths[i] && _paths[i]->bonded()) {
			alloc[i] = (uint8_t)(std::ceil((quality[i] / totQuality) * (float)255));
			_paths[i]->_allocation = alloc[i];
		}
	}
}

void Bond::processBalanceTasks(const int64_t now)
{
	char curPathStr[64] = { 0 };
	char pathStr[64] = { 0 };
	int totalAllocation = 0;
	for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (! _paths[i]) {
			continue;
		}
		if (_paths[i] && _paths[i]->bonded() && _paths[i]->eligible(now, _ackSendInterval)) {
			totalAllocation += _paths[i]->_allocation;
		}
	}
	unsigned char minimumAllocationValue = (uint8_t)(0.33 * ((float)totalAllocation / (float)_numBondedPaths));

	if (_allowFlowHashing) {
		/**
		 * Clean up and reset flows if necessary
		 */
		if ((now - _lastFlowExpirationCheck) > ZT_MULTIPATH_FLOW_CHECK_INTERVAL) {
			Mutex::Lock _l(_flows_m);
			forgetFlowsWhenNecessary(ZT_MULTIPATH_FLOW_EXPIRATION_INTERVAL, false, now);
			_lastFlowExpirationCheck = now;
		}
		if ((now - _lastFlowStatReset) > ZT_FLOW_STATS_RESET_INTERVAL) {
			Mutex::Lock _l(_flows_m);
			_lastFlowStatReset = now;
			std::map<int32_t, SharedPtr<Flow> >::iterator it = _flows.begin();
			while (it != _flows.end()) {
				it->second->resetByteCounts();
				++it;
			}
		}
		/**
		 * Re-allocate flows from dead paths
		 */
		if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_XOR || _bondingPolicy == ZT_BONDING_POLICY_BALANCE_AWARE) {
			Mutex::Lock _l(_flows_m);
			for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
				if (! _paths[i]) {
					continue;
				}
				if (! _paths[i]->eligible(now, _ackSendInterval) && _paths[i]->_shouldReallocateFlows) {
					_paths[i]->address().toString(pathStr);
					log("b*", "reallocate flows from dead link %s/%s", getLink(_paths[i])->ifname().c_str(), pathStr);
					std::map<int32_t, SharedPtr<Flow> >::iterator flow_it = _flows.begin();
					while (flow_it != _flows.end()) {
						if (flow_it->second->assignedPath() == _paths[i]) {
							if (assignFlowToBondedPath(flow_it->second, now)) {
								_paths[i]->_assignedFlowCount--;
							}
						}
						++flow_it;
					}
					_paths[i]->_shouldReallocateFlows = false;
				}
			}
		}
		/**
		 * Re-allocate flows from under-performing
		 * NOTE: This could be part of the above block but was kept separate for clarity.
		 */
		if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_XOR || _bondingPolicy == ZT_BONDING_POLICY_BALANCE_AWARE) {
			Mutex::Lock _l(_flows_m);
			for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
				if (! _paths[i]) {
					continue;
				}
				if (_paths[i] && _paths[i]->bonded() && _paths[i]->eligible(now, _ackSendInterval) && (_paths[i]->_allocation < minimumAllocationValue) && _paths[i]->_assignedFlowCount) {
					_paths[i]->address().toString(curPathStr);
					_paths[i]->address().toString(pathStr);
					log("b*", "reallocate flows from under-performing link %s/%s\n", getLink(_paths[i])->ifname().c_str(), pathStr);
					std::map<int32_t, SharedPtr<Flow> >::iterator flow_it = _flows.begin();
					while (flow_it != _flows.end()) {
						if (flow_it->second->assignedPath() == _paths[i]) {
							if (assignFlowToBondedPath(flow_it->second, now)) {
								_paths[i]->_assignedFlowCount--;
							}
						}
						++flow_it;
					}
					_paths[i]->_shouldReallocateFlows = false;
				}
			}
		}
	}
	/**
	 * Tasks specific to (Balance Round Robin)
	 */
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_RR) {
		// Nothing
	}
	/**
	 * Tasks specific to (Balance XOR)
	 */
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_XOR) {
		// Nothing
	}
	/**
	 * Tasks specific to (Balance Aware)
	 */
	if (_bondingPolicy == ZT_BONDING_POLICY_BALANCE_AWARE) {
		if (_allowFlowHashing) {
			Mutex::Lock _l(_flows_m);
			if (_flowRebalanceStrategy == ZT_MULTIPATH_FLOW_REBALANCE_STRATEGY_PASSIVE) {
				// Do nothing here, this is taken care of in the more general case above.
			}
			if (_flowRebalanceStrategy == ZT_MULTIPATH_FLOW_REBALANCE_STRATEGY_OPPORTUNISTIC) {
				// If the flow is temporarily inactive we should take this opportunity to re-assign the flow if needed.
			}
			if (_flowRebalanceStrategy == ZT_MULTIPATH_FLOW_REBALANCE_STRATEGY_AGGRESSIVE) {
				/**
				 * Return flows to the original path if it has once again become available
				 */
				if ((now - _lastFlowRebalance) > ZT_FLOW_REBALANCE_INTERVAL) {
					std::map<int32_t, SharedPtr<Flow> >::iterator flow_it = _flows.begin();
					while (flow_it != _flows.end()) {
						if (flow_it->second->_previouslyAssignedPath && flow_it->second->_previouslyAssignedPath->eligible(now, _ackSendInterval) && (flow_it->second->_previouslyAssignedPath->_allocation >= (minimumAllocationValue * 2))) {
							// fprintf(stderr, "moving flow back onto its previous path assignment (based on eligibility)\n");
							(flow_it->second->_assignedPath->_assignedFlowCount)--;
							flow_it->second->assignPath(flow_it->second->_previouslyAssignedPath, now);
							(flow_it->second->_previouslyAssignedPath->_assignedFlowCount)++;
						}
						++flow_it;
					}
					_lastFlowRebalance = now;
				}
				/**
				 * Return flows to the original path if it has once again become (performant)
				 */
				if ((now - _lastFlowRebalance) > ZT_FLOW_REBALANCE_INTERVAL) {
					std::map<int32_t, SharedPtr<Flow> >::iterator flow_it = _flows.begin();
					while (flow_it != _flows.end()) {
						if (flow_it->second->_previouslyAssignedPath && flow_it->second->_previouslyAssignedPath->eligible(now, _ackSendInterval) && (flow_it->second->_previouslyAssignedPath->_allocation >= (minimumAllocationValue * 2))) {
							// fprintf(stderr, "moving flow back onto its previous path assignment (based on performance)\n");
							(flow_it->second->_assignedPath->_assignedFlowCount)--;
							flow_it->second->assignPath(flow_it->second->_previouslyAssignedPath, now);
							(flow_it->second->_previouslyAssignedPath->_assignedFlowCount)++;
						}
						++flow_it;
					}
					_lastFlowRebalance = now;
				}
			}
		}
		else if (! _allowFlowHashing) {
			// Nothing
		}
	}
}

void Bond::dequeueNextActiveBackupPath(const uint64_t now)
{
	if (_abFailoverQueue.empty()) {
		return;
	}
	_abPath = _abFailoverQueue.front();
	_abFailoverQueue.pop_front();
	_lastActiveBackupPathChange = now;
	for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (_paths[i]) {
			_paths[i]->resetPacketCounts();
		}
	}
}

bool Bond::abForciblyRotateLink()
{
	char prevPathStr[64];
	char curPathStr[64];
	if (_bondingPolicy == ZT_BONDING_POLICY_ACTIVE_BACKUP) {
		SharedPtr<Path> prevPath = _abPath;
		_abPath->address().toString(prevPathStr);
		dequeueNextActiveBackupPath(RR->node->now());
		_abPath->address().toString(curPathStr);
		log("ab", "forcibly rotate link from %s/%s to %s/%s", getLink(prevPath)->ifname().c_str(), prevPathStr, getLink(_abPath)->ifname().c_str(), curPathStr);
		return true;
	}
	return false;
}

void Bond::processActiveBackupTasks(void* tPtr, const int64_t now)
{
	char pathStr[64] = { 0 };
	char prevPathStr[64];
	char curPathStr[64];
	SharedPtr<Path> prevActiveBackupPath = _abPath;
	SharedPtr<Path> nonPreferredPath;
	bool bFoundPrimaryLink = false;

	/**
	 * Generate periodic status report
	 */
	if ((now - _lastBondStatusLog) > ZT_MULTIPATH_BOND_STATUS_INTERVAL) {
		_lastBondStatusLog = now;
		if (_abPath) {
			_abPath->address().toString(curPathStr);
			log("ab", "active link is %s/%s, failover queue size is %zu", getLink(_abPath)->ifname().c_str(), curPathStr, _abFailoverQueue.size());
		}
		else {
			log("ab", "no active link");
		}
		if (_abFailoverQueue.empty()) {
			log("ab", "failover queue is empty, no longer fault-tolerant");
		}
	}
	/**
	 * Select initial "active" active-backup link
	 */
	if (! _abPath) {
		/**
		 * [Automatic mode]
		 * The user has not explicitly specified links or their failover schedule,
		 * the bonding policy will now select the first eligible path and set it as
		 * its active backup path, if a substantially better path is detected the bonding
		 * policy will assign it as the new active backup path. If the path fails it will
		 * simply find the next eligible path.
		 */
		if (! userHasSpecifiedLinks()) {
			log("ab", "no user-specified links");
			for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
				if (_paths[i] && _paths[i]->eligible(now, _ackSendInterval)) {
					_paths[i]->address().toString(curPathStr);
					SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
					if (link) {
						log("ab", "found eligible link %s/%s", getLink(_paths[i])->ifname().c_str(), curPathStr);
					}
					_abPath = _paths[i];
					break;
				}
			}
		}
		/**
		 * [Manual mode]
		 * The user has specified links or failover rules that the bonding policy should adhere to.
		 */
		else if (userHasSpecifiedLinks()) {
			if (userHasSpecifiedPrimaryLink()) {
				for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
					if (! _paths[i]) {
						continue;
					}
					SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
					if (_paths[i]->eligible(now, _ackSendInterval) && link->primary()) {
						if (! _paths[i]->preferred()) {
							_paths[i]->address().toString(curPathStr);
							// Found path on primary link, take note in case we don't find a preferred path
							nonPreferredPath = _paths[i];
							bFoundPrimaryLink = true;
						}
						if (_paths[i]->preferred()) {
							_abPath = _paths[i];
							_abPath->address().toString(curPathStr);
							SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
							bFoundPrimaryLink = true;
							break;	 // Found preferred path %s on primary link
						}
					}
				}
				if (_abPath) {
					_abPath->address().toString(curPathStr);
					SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _abPath->localSocket());
					if (link) {
						log("ab", "found preferred primary link %s/%s", getLink(_abPath)->ifname().c_str(), curPathStr);
					}
				}
				else {
					if (bFoundPrimaryLink && nonPreferredPath) {
						log("ab", "found non-preferred primary link");
						_abPath = nonPreferredPath;
					}
				}
				if (! _abPath) {
					log("ab", "user-designated primary link is not yet ready");
					// TODO: Should wait for some time (failover interval?) and then switch to spare link
				}
			}
			else if (! userHasSpecifiedPrimaryLink()) {
				int _abIdx = ZT_MAX_PEER_NETWORK_PATHS;
				log("ab", "user did not specify a primary link, select first available link");
				for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
					if (_paths[i] && _paths[i]->eligible(now, _ackSendInterval)) {
						_abIdx = i;
						break;
					}
				}
				if (_abIdx == ZT_MAX_PEER_NETWORK_PATHS) {
					// Unable to find a candidate next-best, no change
				}
				else {
					_abPath = _paths[_abIdx];
					SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _abPath->localSocket());
					if (link) {
						_abPath->address().toString(curPathStr);
						log("ab", "select non-primary link %s/%s", getLink(_abPath)->ifname().c_str(), curPathStr);
					}
				}
			}
		}
	}
	/**
	 * Update and maintain the active-backup failover queue
	 */
	if (_abPath) {
		// Don't worry about the failover queue until we have an active link
		// Remove ineligible paths from the failover link queue
		for (std::list<SharedPtr<Path> >::iterator it(_abFailoverQueue.begin()); it != _abFailoverQueue.end();) {
			if ((*it) && ! (*it)->eligible(now, _ackSendInterval)) {
				(*it)->address().toString(curPathStr);
				SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, (*it)->localSocket());
				it = _abFailoverQueue.erase(it);
				if (link) {
					log("ab", "link %s/%s is now ineligible, removing from failover queue (%zu links in queue)", getLink(_abPath)->ifname().c_str(), curPathStr, _abFailoverQueue.size());
				}
			}
			else {
				++it;
			}
		}
		/**
		 * Failover instructions were provided by user, build queue according those as well as IPv
		 * preference, disregarding performance.
		 */
		if (userHasSpecifiedFailoverInstructions()) {
			/**
			 * Clear failover scores
			 */
			for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
				if (_paths[i]) {
					_paths[i]->_failoverScore = 0;
				}
			}
			// Follow user-specified failover instructions
			for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
				if (! _paths[i] || ! _paths[i]->allowed() || ! _paths[i]->eligible(now, _ackSendInterval)) {
					continue;
				}
				SharedPtr<Link> link = RR->bc->getLinkBySocket(_policyAlias, _paths[i]->localSocket());
				_paths[i]->address().toString(pathStr);

				int failoverScoreHandicap = _paths[i]->_failoverScore;
				if (_paths[i]->preferred()) {
					failoverScoreHandicap += ZT_MULTIPATH_FAILOVER_HANDICAP_PREFERRED;
				}
				if (link->primary()) {
					// If using "optimize" primary re-select mode, ignore user link designations
					failoverScoreHandicap += ZT_MULTIPATH_FAILOVER_HANDICAP_PRIMARY;
				}
				if (! _paths[i]->_failoverScore) {
					// If we didn't inherit a failover score from a "parent" that wants to use this path as a failover
					int newHandicap = failoverScoreHandicap ? failoverScoreHandicap : _paths[i]->_allocation;
					_paths[i]->_failoverScore = newHandicap;
				}
				SharedPtr<Link> failoverLink;
				if (link->failoverToLink().length()) {
					failoverLink = RR->bc->getLinkByName(_policyAlias, link->failoverToLink());
				}
				if (failoverLink) {
					for (int j = 0; j < ZT_MAX_PEER_NETWORK_PATHS; j++) {
						if (_paths[j] && getLink(_paths[j]) == failoverLink.ptr()) {
							_paths[j]->address().toString(pathStr);
							int inheritedHandicap = failoverScoreHandicap - 10;
							int newHandicap = _paths[j]->_failoverScore > inheritedHandicap ? _paths[j]->_failoverScore : inheritedHandicap;
							if (! _paths[j]->preferred()) {
								newHandicap--;
							}
							_paths[j]->_failoverScore = newHandicap;
						}
					}
				}
				if (_paths[i].ptr() != _abPath.ptr()) {
					bool bFoundPathInQueue = false;
					for (std::list<SharedPtr<Path> >::iterator it(_abFailoverQueue.begin()); it != _abFailoverQueue.end(); ++it) {
						if (_paths[i].ptr() == (*it).ptr()) {
							bFoundPathInQueue = true;
						}
					}
					if (! bFoundPathInQueue) {
						_abFailoverQueue.push_front(_paths[i]);
						_paths[i]->address().toString(curPathStr);
						log("ab", "add link %s/%s to failover queue (%zu links in queue)", getLink(_abPath)->ifname().c_str(), curPathStr, _abFailoverQueue.size());
					}
				}
			}
		}
		/**
		 * No failover instructions provided by user, build queue according to performance
		 * and IPv preference.
		 */
		else if (! userHasSpecifiedFailoverInstructions()) {
			for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
				if (! _paths[i] || ! _paths[i]->allowed() || ! _paths[i]->eligible(now, _ackSendInterval)) {
					continue;
				}
				int failoverScoreHandicap = 0;
				if (_paths[i]->preferred()) {
					failoverScoreHandicap = ZT_MULTIPATH_FAILOVER_HANDICAP_PREFERRED;
				}
				bool includeRefractoryPeriod = true;
				if (! _paths[i]->eligible(now, includeRefractoryPeriod)) {
					failoverScoreHandicap = -10000;
				}
				if (getLink(_paths[i])->primary() && _abLinkSelectMethod != ZT_MULTIPATH_RESELECTION_POLICY_OPTIMIZE) {
					// If using "optimize" primary reselect mode, ignore user link designations
					failoverScoreHandicap = ZT_MULTIPATH_FAILOVER_HANDICAP_PRIMARY;
				}
				if (_paths[i].ptr() == negotiatedPath.ptr()) {
					_paths[i]->_negotiated = true;
					failoverScoreHandicap = ZT_MULTIPATH_FAILOVER_HANDICAP_NEGOTIATED;
				}
				else {
					_paths[i]->_negotiated = false;
				}
				_paths[i]->_failoverScore = _paths[i]->_allocation + failoverScoreHandicap;
				if (_paths[i].ptr() != _abPath.ptr()) {
					bool bFoundPathInQueue = false;
					for (std::list<SharedPtr<Path> >::iterator it(_abFailoverQueue.begin()); it != _abFailoverQueue.end(); ++it) {
						if (_paths[i].ptr() == (*it).ptr()) {
							bFoundPathInQueue = true;
						}
					}
					if (! bFoundPathInQueue) {
						_abFailoverQueue.push_front(_paths[i]);
						_paths[i]->address().toString(curPathStr);
						log("ab", "add link %s/%s to failover queue (%zu links in queue)", getLink(_paths[i])->ifname().c_str(), curPathStr, _abFailoverQueue.size());
					}
				}
			}
		}
		_abFailoverQueue.sort(PathQualityComparator());
	}
	/**
	 * Short-circuit if we have no queued paths
	 */
	if (_abFailoverQueue.empty()) {
		return;
	}
	/**
	 * Fulfill primary re-select obligations
	 */
	if (_abPath && ! _abPath->eligible(now, _ackSendInterval)) {   // Implicit ZT_MULTIPATH_RESELECTION_POLICY_FAILURE
		_abPath->address().toString(curPathStr);
		log("ab", "link %s/%s has failed, select link from failover queue (%zu links in queue)", getLink(_abPath)->ifname().c_str(), curPathStr, _abFailoverQueue.size());
		if (! _abFailoverQueue.empty()) {
			dequeueNextActiveBackupPath(now);
			_abPath->address().toString(curPathStr);
			log("ab", "active link switched to %s/%s", getLink(_abPath)->ifname().c_str(), curPathStr);
		}
		else {
			log("ab", "failover queue is empty, no links to choose from");
		}
	}
	/**
	 * Detect change to prevent flopping during later optimization step.
	 */
	if (prevActiveBackupPath != _abPath) {
		_lastActiveBackupPathChange = now;
	}
	if (_abLinkSelectMethod == ZT_MULTIPATH_RESELECTION_POLICY_ALWAYS) {
		if (_abPath && ! getLink(_abPath)->primary() && getLink(_abFailoverQueue.front())->primary()) {
			dequeueNextActiveBackupPath(now);
			_abPath->address().toString(curPathStr);
			log("ab", "switch back to available primary link %s/%s (select: always)", getLink(_abPath)->ifname().c_str(), curPathStr);
		}
	}
	if (_abLinkSelectMethod == ZT_MULTIPATH_RESELECTION_POLICY_BETTER) {
		if (_abPath && ! getLink(_abPath)->primary()) {
			// Active backup has switched to "better" primary link according to re-select policy.
			if (getLink(_abFailoverQueue.front())->primary() && (_abFailoverQueue.front()->_failoverScore > _abPath->_failoverScore)) {
				dequeueNextActiveBackupPath(now);
				_abPath->address().toString(curPathStr);
				log("ab", "switch back to user-defined primary link %s/%s (select: better)", getLink(_abPath)->ifname().c_str(), curPathStr);
			}
		}
	}
	if (_abLinkSelectMethod == ZT_MULTIPATH_RESELECTION_POLICY_OPTIMIZE && ! _abFailoverQueue.empty()) {
		/**
		 * Implement link negotiation that was previously-decided
		 */
		if (_abFailoverQueue.front()->_negotiated) {
			dequeueNextActiveBackupPath(now);
			_abPath->address().toString(prevPathStr);
			_lastPathNegotiationCheck = now;
			_abPath->address().toString(curPathStr);
			log("ab", "switch negotiated link %s/%s (select: optimize)", getLink(_abPath)->ifname().c_str(), curPathStr);
		}
		else {
			// Try to find a better path and automatically switch to it -- not too often, though.
			if ((now - _lastActiveBackupPathChange) > ZT_MULTIPATH_MIN_ACTIVE_BACKUP_AUTOFLOP_INTERVAL) {
				if (! _abFailoverQueue.empty()) {
					int newFScore = _abFailoverQueue.front()->_failoverScore;
					int prevFScore = _abPath->_failoverScore;
					// Establish a minimum switch threshold to prevent flapping
					int failoverScoreDifference = _abFailoverQueue.front()->_failoverScore - _abPath->_failoverScore;
					int thresholdQuantity = (int)(ZT_MULTIPATH_ACTIVE_BACKUP_OPTIMIZE_MIN_THRESHOLD * (float)_abPath->_allocation);
					if ((failoverScoreDifference > 0) && (failoverScoreDifference > thresholdQuantity)) {
						SharedPtr<Path> oldPath = _abPath;
						_abPath->address().toString(prevPathStr);
						dequeueNextActiveBackupPath(now);
						_abPath->address().toString(curPathStr);
						log("ab",
							"switch from %s/%s (score: %d) to better link %s/%s (score: %d) for peer %llx (select: optimize)",
							getLink(oldPath)->ifname().c_str(),
							prevPathStr,
							prevFScore,
							getLink(_abPath)->ifname().c_str(),
							curPathStr,
							newFScore,
							_peerId);
					}
				}
			}
		}
	}
}

void Bond::setReasonableDefaults(int policy, SharedPtr<Bond> templateBond, bool useTemplate)
{
	// If invalid bonding policy, try default
	int _defaultBondingPolicy = BondController::defaultBondingPolicy();
	if (policy <= ZT_BONDING_POLICY_NONE || policy > ZT_BONDING_POLICY_BALANCE_AWARE) {
		// If no default set, use NONE (effectively disabling this bond)
		if (_defaultBondingPolicy < ZT_BONDING_POLICY_NONE || _defaultBondingPolicy > ZT_BONDING_POLICY_BALANCE_AWARE) {
			_bondingPolicy = ZT_BONDING_POLICY_NONE;
		}
		_bondingPolicy = _defaultBondingPolicy;
	}
	else {
		_bondingPolicy = policy;
	}

	_freeRandomByte = 0;

	_userHasSpecifiedPrimaryLink = false;
	_userHasSpecifiedFailoverInstructions = false;

	_isHealthy = false;
	_numAliveLinks = 0;
	_numTotalLinks = 0;

	_downDelay = 0;
	_upDelay = 0;
	_allowFlowHashing = false;
	_bondMonitorInterval = 0;
	_shouldCollectPathStatistics = false;

	// Path negotiation
	_allowPathNegotiation = false;
	_pathNegotiationCutoffCount = 0;
	_localUtility = 0;

	_numBondedPaths = 0;
	_rrPacketsSentOnCurrLink = 0;
	_rrIdx = 0;

	_totalBondUnderload = 0;

	_maxAcceptableLatency = 100;
	_maxAcceptablePacketDelayVariance = 50;
	_maxAcceptablePacketLossRatio = 0.10f;
	_maxAcceptablePacketErrorRatio = 0.10f;
	_userHasSpecifiedLinkSpeeds = 0;

	/* ZT_MULTIPATH_FLOW_REBALANCE_STRATEGY_PASSIVE is the most conservative strategy and is
	least likely to cause unexpected behavior */
	_flowRebalanceStrategy = ZT_MULTIPATH_FLOW_REBALANCE_STRATEGY_AGGRESSIVE;

	/**
	 * Paths are actively monitored to provide a real-time quality/preference-ordered rapid failover queue.
	 */
	switch (policy) {
		case ZT_BONDING_POLICY_ACTIVE_BACKUP:
			_failoverInterval = 500;
			_abLinkSelectMethod = ZT_MULTIPATH_RESELECTION_POLICY_OPTIMIZE;
			_linkMonitorStrategy = ZT_MULTIPATH_SLAVE_MONITOR_STRATEGY_DYNAMIC;
			_qualityWeights[ZT_QOS_LAT_IDX] = 0.2f;
			_qualityWeights[ZT_QOS_LTM_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_PDV_IDX] = 0.2f;
			_qualityWeights[ZT_QOS_PLR_IDX] = 0.2f;
			_qualityWeights[ZT_QOS_PER_IDX] = 0.2f;
			_qualityWeights[ZT_QOS_THR_IDX] = 0.2f;
			_qualityWeights[ZT_QOS_THM_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_THV_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_SCP_IDX] = 0.0f;
			break;
		/**
		 * All seemingly-alive paths are used. Paths are not actively monitored.
		 */
		case ZT_BONDING_POLICY_BROADCAST:
			_downDelay = 30000;
			_upDelay = 0;
			break;
		/**
		 * Paths are monitored to determine when/if one needs to be added or removed from the rotation
		 */
		case ZT_BONDING_POLICY_BALANCE_RR:
			_failoverInterval = 3000;
			_allowFlowHashing = false;
			_packetsPerLink = 1024;
			_linkMonitorStrategy = ZT_MULTIPATH_SLAVE_MONITOR_STRATEGY_DYNAMIC;
			_qualityWeights[ZT_QOS_LAT_IDX] = 0.4f;
			_qualityWeights[ZT_QOS_LTM_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_PDV_IDX] = 0.2f;
			_qualityWeights[ZT_QOS_PLR_IDX] = 0.1f;
			_qualityWeights[ZT_QOS_PER_IDX] = 0.1f;
			_qualityWeights[ZT_QOS_THR_IDX] = 0.1f;
			_qualityWeights[ZT_QOS_THM_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_THV_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_SCP_IDX] = 0.0f;
			break;
		/**
		 * Path monitoring is used to determine the capacity of each
		 * path and where to place the next flow.
		 */
		case ZT_BONDING_POLICY_BALANCE_XOR:
			_failoverInterval = 3000;
			_upDelay = _bondMonitorInterval * 2;
			_allowFlowHashing = true;
			_linkMonitorStrategy = ZT_MULTIPATH_SLAVE_MONITOR_STRATEGY_DYNAMIC;
			_qualityWeights[ZT_QOS_LAT_IDX] = 0.4f;
			_qualityWeights[ZT_QOS_LTM_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_PDV_IDX] = 0.2f;
			_qualityWeights[ZT_QOS_PLR_IDX] = 0.1f;
			_qualityWeights[ZT_QOS_PER_IDX] = 0.1f;
			_qualityWeights[ZT_QOS_THR_IDX] = 0.1f;
			_qualityWeights[ZT_QOS_THM_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_THV_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_SCP_IDX] = 0.0f;
			break;
		/**
		 * Path monitoring is used to determine the capacity of each
		 * path and where to place the next flow. Additionally, re-shuffling
		 * of flows may take place.
		 */
		case ZT_BONDING_POLICY_BALANCE_AWARE:
			_failoverInterval = 3000;
			_allowFlowHashing = true;
			_linkMonitorStrategy = ZT_MULTIPATH_SLAVE_MONITOR_STRATEGY_DYNAMIC;
			_qualityWeights[ZT_QOS_LAT_IDX] = 0.4f;
			_qualityWeights[ZT_QOS_LTM_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_PDV_IDX] = 0.4f;
			_qualityWeights[ZT_QOS_PLR_IDX] = 0.2f;
			_qualityWeights[ZT_QOS_PER_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_THR_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_THM_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_THV_IDX] = 0.0f;
			_qualityWeights[ZT_QOS_SCP_IDX] = 0.0f;
			break;
		default:
			break;
	}

	/* If a user has specified custom parameters for this bonding policy, overlay
	them onto the defaults that were previously set */
	if (useTemplate) {
		_policyAlias = templateBond->_policyAlias;
		_failoverInterval = templateBond->_failoverInterval >= 250 ? templateBond->_failoverInterval : _failoverInterval;
		_downDelay = templateBond->_downDelay;
		_upDelay = templateBond->_upDelay;
		if (templateBond->_linkMonitorStrategy == ZT_MULTIPATH_SLAVE_MONITOR_STRATEGY_PASSIVE && templateBond->_failoverInterval != 0) {
			// fprintf(stderr, "warning: passive path monitoring was specified, this will prevent failovers from happening in a timely manner.\n");
		}
		_abLinkSelectMethod = templateBond->_abLinkSelectMethod;
		memcpy(_qualityWeights, templateBond->_qualityWeights, ZT_QOS_WEIGHT_SIZE * sizeof(float));
	}

	/* Set timer geometries */
	_bondMonitorInterval = _failoverInterval / 3;
	BondController::setMinReqPathMonitorInterval(_bondMonitorInterval);
	_ackSendInterval = _failoverInterval;
	_qualityEstimationInterval = _failoverInterval * 2;
	_dynamicPathMonitorInterval = 0;
	_ackCutoffCount = 0;
	_qosSendInterval = _bondMonitorInterval * 4;
	_qosCutoffCount = 0;
	throughputMeasurementInterval = _ackSendInterval * 2;
	_defaultPathRefractoryPeriod = 8000;
}

void Bond::setUserQualityWeights(float weights[], int len)
{
	if (len == ZT_QOS_WEIGHT_SIZE) {
		float weightTotal = 0.0;
		for (unsigned int i = 0; i < ZT_QOS_WEIGHT_SIZE; ++i) {
			weightTotal += weights[i];
		}
		if (weightTotal > 0.99 && weightTotal < 1.01) {
			memcpy(_qualityWeights, weights, len * sizeof(float));
		}
	}
}

SharedPtr<Link> Bond::getLink(const SharedPtr<Path>& path)
{
	return RR->bc->getLinkBySocket(_policyAlias, path->localSocket());
}

void Bond::dumpPathStatus(const int64_t now, const SharedPtr<Path>& path, int idx = -1)
{
	char pathStr[64] = { 0 };
	path->address().toString(pathStr);
	log("bond",
		"path status: [%2d] alive:%d, eli:%d, bonded:%d, flows:%5d, lat:   %5.4f, jitter:  %5.4f, error:  %5.4f, loss:  %5.4f, age:  %6d, ack: %6d --- (%s/%s)",
		idx,
		path->alive(now, true),
		path->eligible(now, _ackSendInterval),
		path->bonded(),
		path->_assignedFlowCount,
		path->latencyMean(),
		path->latencyVariance(),
		path->packetErrorRatio(),
		path->packetLossRatio(),
		path->age(now),
		path->ackAge(now),
		getLink(path)->ifname().c_str(),
		pathStr);
}

void Bond::dumpInfo(const int64_t now, bool force)
{
	if (! force && (now - _lastSummaryDump) < (ZT_MULTIPATH_BOND_STATUS_INTERVAL)) {
		return;
	}
	_lastSummaryDump = now;
	log("bond", "bond status: asi: %d, mi: %d, ud: %d, dd: %d, flows: %lu", _ackSendInterval, _bondMonitorInterval, _upDelay, _downDelay, (unsigned long)_flows.size());
	for (int i = 0; i < ZT_MAX_PEER_NETWORK_PATHS; ++i) {
		if (_paths[i]) {
			dumpPathStatus(now, _paths[i], i);
		}
	}
}

}	// namespace ZeroTier

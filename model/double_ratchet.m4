// This is a Tamarin model of Signal's double ratchet with a clone-detection
// mechanism. Communicating parties can suffer from state loss (single-state 
// loss and total-state loss) and an attacker can impersonate a user by 
// cloning their device.

dnl Lines starting with 'dnl' are comments for the preprocessor m4.

dnl Tamarin uses '', which is an m4 close quote, so use <! !> for quoting.
changequote(<!,!>)
changecom(<!/*!>, <!*/!>)

define(WITH_SINGLE_STATE_LOSS, true)
define(WITH_TOTAL_STATE_LOSS, true)
define(CUSTOM_NETWORK, true)

define(kNull, 'NULL')
define(kMessageChain, 'CONSTANT')
define(kSending, 'SENDING')
define(kReceiving, 'RECEIVING')
define(kInitInitializer, 'INIT_INITIALIZER')
define(kInitResponder, 'INIT_RESPONDER')
define(kInitializationStart, 'INITIALIZATION_STARTED')
define(kZero, '0')
define(kFirst, '1')
define(kSecond, '2')
define(kRK, 'RK')
define(kNullRootKey, KDF(kFirst, kRK, 'NULL'))
define(kNullSndChainKey, KDF(kFirst, kMessageChain, 'NULL'))
define(kNullRcvChainKey, KDF(kFirst, kMessageChain, 'NULL'))
define(kEmptySet, 'empty')
define(UserStateFacts,
<!
    UserState($*)
  , UserData($*)
!>)

theory double_ratchet 

begin

functions: MAC/2, KDF/3, h/1
builtins: diffie-hellman, symmetric-encryption, multiset

// BEGIN Restrictions

restriction at_most_one_association_per_pair_of_users:
    "All userA userB #i #j.
     AssociateUsers(userA, userB) @ i &
     AssociateUsers(userA, userB) @ j
     ==> #i = #j"

restriction users_cannot_associate_with_themselves:
    "All user #i. AssociateUsers(user, user) @ i ==> F"

restriction no_parallel_initializations:
    "All userThread1 userThread2 user partner epochKey1 epochKey2 
     #i1 #i2 #j1 #j2.
     StartInitialize(userThread1, user, partner, epochKey1) @ i1 &
     StartInitialize(userThread2, partner, user, epochKey1) @ i2 &
     StartInitialize(userThread1, user, partner, epochKey2) @ j1 &
     StartInitialize(userThread2, partner, user, epochKey2) @ j2 &
     not epochKey1 = epochKey2
     ==> (i1 < j1 & i1 < j2 & i2 < j1 & i2 < j2) |
         (j1 < i1 & j1 < i2 & j2 < i1 & j2 < i2)"

restriction messages_are_in_order:
    "All senderThread receiverThread sender receiver payload1 payload2 
     #i1 #i2 #j1 #j2. i1 < i2 &
     SendPayload(senderThread, sender, receiver, payload1) @ i1 & 
     SendPayload(senderThread, sender, receiver, payload2) @ i2 &
     ReceivePayload(receiverThread, receiver, sender, payload1) @ j1 & 
     ReceivePayload(receiverThread, receiver, sender, payload2) @ j2
     ==> j1 < j2"

restriction equality:
    "All x y #i. Eq(x, y) @ i ==> x = y"

restriction inequality:
    "All x y #i. Neq(x, y) @ i ==> not(x = y)"

restriction invalid_mac:
    "All x y #i. InvalidMAC(x, y) @ i ==> not(x = y)"

restriction detect_low_counters:
    "All currentRcvCtr inRcvCtr #i.
     MessageNumberIsTooLow(currentRcvCtr, inRcvCtr) @ i
     ==>
     Ex x. currentRcvCtr = inRcvCtr + x"

// END Restrictions

// BEGIN Communication Channels

define(Send, ifelse(CUSTOM_NETWORK, true, <!Out$1($2, $3, $4)!>, <!Out($4)!>))
define(Receive, ifelse(CUSTOM_NETWORK, true, <!Rcv($1, $2, $3)[no_precomp]!>, <!In($3)!>))
define(SendRule, ifelse(CUSTOM_NETWORK, true, <!
rule Out_$1 [color=ffffff]:
    [ Send($1, $2, $3, message) ]
    --[]->
    [ Receive($3, $2, message) ]!>,))

// END Communication Channels

// BEGIN Setup

rule CreateUser [color=ffb433]:
    [ Fr(~userID) ]
    --[ CreateUser(~userID) ]->
    [ !User(~userID) ]

rule AssociateUsers [color=ffb433]:
    [ !User(~userA)
    , !User(~userB) ]
    --[ AssociateUsers(~userA, ~userB)
      , AssociateUsers(~userB, ~userA) ]->
    [ StartUser(~userA, ~userB, kInitInitializer)
    , StartUser(~userB, ~userA, kInitResponder) ]

rule CommunicationStartWithPartner [color=ffb433]:
    let
        dummyPartnerPublicKey = 'g'^~dummyPartnerPrivateKey
        rootKey = kNullRootKey
        prevRootKey = kNullRootKey
        privateKey = ~dummyPrivateKey
        partnerPublicKey = dummyPartnerPublicKey
        rcvChainKey = kNullRcvChainKey
        prevRcvChainKey = kNullRcvChainKey
        sndChainKey = kNullSndChainKey
        rcvCtr = kZero
        sndCtr = kZero + '0'
        dummyEpochKey = h(rootKey)
    in
    [ StartUser(~user, ~partner, state)
    , Fr(~userThread)
    , Fr(~dummyPrivateKey)
    , Fr(~dummyPartnerPrivateKey) ]
    --[ StartChain(~userThread, ~user, ~partner) ]->
    [ UserState(~userThread, ~user, ~partner, state, rootKey,
                privateKey, partnerPublicKey, rcvChainKey, sndChainKey, 
                dummyEpochKey, sndCtr, rcvCtr, prevRootKey, prevRcvChainKey) ]

rule InitInitiatorStart [color=f5e642]:
    let 
        rootKey = KDF(kFirst, kRK, ~rk)
        nullPrevRootKey = kNullRootKey
        nullPrevRcvChainKey = kNullRcvChainKey
        publicKey = 'g'^~privateKey
        epochKey = h(rootKey)
        rcvCtrZero = kZero
        sndCtrZero = kZero + '0'
    in
    [ UserState(~userThread, ~user, ~partner, kInitInitializer, oldRootKey, 
                ~oldPrivateKey, oldPartnerPublicKey, rcvChainKey, sndChainKey,
                oldEpochKey, sndCtr, rcvCtr, 
                oldPrevRootKey, oldPrevRcvChainKey)[no_precomp]
    , Fr(~rk)
    , Fr(~privateKey)
    , Fr(~initiatorToken) ]
    --[ Step(~userThread, ~user, ~partner)
      , StartInitialize(~userThread, ~user, ~partner, epochKey)
      , SendPayload(~userThread, ~user, ~partner, rootKey) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kInitializationStart, rootKey, 
                     ~privateKey, oldPartnerPublicKey, 
                     kNullRcvChainKey, kNullSndChainKey, 
                     epochKey, sndCtrZero, rcvCtrZero, 
                     nullPrevRootKey, nullPrevRcvChainKey)
    , InitDataInitiator(~partner, ~user, rootKey, publicKey) ]

rule InitResponder [color=f5e642]:
    let 
        nullPrevRootKey = kNullRootKey
        nullPrevRcvChainKey = kNullRcvChainKey
        publicKey = 'g'^~privateKey
        epochKey = h(rootKey)
        rcvCtrZero = kZero
        sndCtrZero = kZero + '0'
    in
    [ UserState(~userThread, ~user, ~partner, state, oldRootKey, 
                ~oldPrivateKey, oldPartnerPublicKey, rcvChainKey, sndChainKey,
                oldEpochKey, sndCtr, rcvCtr, 
                oldPrevRootKey, oldPrevRcvChainKey)[no_precomp]
    , InitDataInitiator(~user, ~partner, rootKey, partnerPublicKey)
    , Fr(~privateKey)
    , Fr(~responderToken) ]
    --[ StartInitialize(~userThread, ~user, ~partner, epochKey)
      , Initialized(~userThread, ~user, ~partner, epochKey)
      , Step(~userThread, ~user, ~partner)
      , ReceivePayload(~userThread, ~user, ~partner, rootKey)
      , SendPayload(~userThread, ~user, ~partner, rootKey) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kSending, rootKey, 
                     ~privateKey, partnerPublicKey,
                     kNullRcvChainKey, kNullSndChainKey, epochKey, 
                     sndCtrZero, rcvCtrZero, 
                     nullPrevRootKey, nullPrevRcvChainKey)
    , InitDataResponder(~partner, ~user, rootKey, publicKey) ]

rule InitInitiatorFinish [color=f5e642]:
    let 
        nullPrevRootKey = kNullRootKey
        nullPrevRcvChainKey = kNullRcvChainKey
        epochKey = h(rootKey)
        rcvCtrZero = kZero
        sndCtrZero = kZero + '0'
    in
    [ UserState(~userThread, ~user, ~partner, kInitializationStart, rootKey, 
                ~privateKey, oldPartnerPublicKey, 
                kNullRcvChainKey, kNullSndChainKey, epochKey, 
                sndCtrZero, rcvCtrZero, 
                nullPrevRootKey, nullPrevRcvChainKey)
    , InitDataResponder(~user, ~partner, rootKey, partnerPublicKey) ]
    --[ Initialized(~userThread, ~user, ~partner, epochKey)
      , ChainStep(~userThread, ~user, ~partner, epochKey, sndCtrZero, rcvCtrZero)
      , Step(~userThread, ~user, ~partner)
      , ReceivePayload(~userThread, ~user, ~partner, rootKey) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kReceiving, rootKey, 
                     ~privateKey, partnerPublicKey, 
                     kNullRcvChainKey, kNullSndChainKey, epochKey, 
                     sndCtrZero, rcvCtrZero, 
                     nullPrevRootKey, nullPrevRcvChainKey) ]

// END Setup

// BEGIN Double Ratchet with Single-State Loss and Clone Detection

define(StartSenderKeyChainRule,
<!
rule SendStartKeyChain$1 [color=$2]:
    let
        dhOut = partnerPublicKey^~newPrivateKey
        publicKey = 'g'^~newPrivateKey
        rootKey = KDF(kFirst, oldDhOut, rk)
        nextRootKey = KDF(kFirst, dhOut, rootKey)
        sndChainKey = KDF(kFirst, kMessageChain, oldSndChainKey)
        rcvChainKey = KDF(kFirst, kMessageChain, oldRcvChainKey)
        newSndChainKey = KDF(kSecond, dhOut, rootKey)
        nextSndChainKey = KDF(kFirst, kMessageChain, newSndChainKey)
        nextMessageKey = KDF(kSecond, kMessageChain, newSndChainKey)
        message = <senc(~msgPayload, nextMessageKey), publicKey, sndCtr>
        messageMAC = MAC(message, epochKey)
    in
    [ UserState(~userThread, ~user, ~partner, kReceiving, rootKey, ~privateKey, 
                partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
                sndCtr, rcvCtr, prevRootKey, prevRcvChainKey)[no_precomp]
    , Fr(~newPrivateKey)
    , Fr(~msgPayload) ]
    --[ StartSenderKeyChain$1(~userThread, $4, $5, partnerPublicKey,
                              rcvChainKey, $6)
      , StartKeyChain(~userThread, $4, $5, partnerPublicKey, rcvChainKey, $6)
      , SendsMessage(~userThread, ~user, ~partner, message, epochKey, sndCtr)
      , SendsMessage$1(~userThread, ~user, ~partner, message)
      , ChainStep(~userThread, ~user, ~partner, epochKey, sndCtr, rcvCtr)
      , SendReceiveStep(~userThread, ~user, ~partner, epochKey, sndCtr)
      , Step(~userThread, ~user, ~partner)
      , SendPayload(~userThread, ~user, ~partner, ~msgPayload) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, $3, $4, $5, 
                     partnerPublicKey, rcvChainKey, $6, epochKey, $7, 
                     rcvCtr, prevRootKey, prevRcvChainKey)
    , Send(SendStartKeyChain$1, ~user, ~partner, <!<message, messageMAC>!>) ]

SendRule(SendStartKeyChain$1, ~user, ~partner)
!>)

StartSenderKeyChainRule(Normal, c1fa70, kSending, nextRootKey, 
                        ~newPrivateKey, nextSndChainKey, sndCtr + '0')

ifelse(WITH_SINGLE_STATE_LOSS, true,
<!StartSenderKeyChainRule(StateLoss, ea70fa, kReceiving, rootKey,
                          ~privateKey, sndChainKey, sndCtr)!>,)

define(SendMessageRule,
<!
rule SendMessage$1 [color=$2]:
    let
        publicKey = 'g'^~privateKey
        rootKey = KDF(kFirst, dhOut, rk)
        sndChainKey = KDF(kFirst, something, oldSndChainKey)
        rcvChainKey = KDF(kFirst, something, oldRcvChainKey)
        nextSndChainKey = KDF(kFirst, kMessageChain, sndChainKey)
        nextMessageKey = KDF(kSecond, kMessageChain, sndChainKey)
        message = <senc(~msgPayload, nextMessageKey), publicKey, sndCtr>
        messageMAC = MAC(message, epochKey)
    in
    [ UserState(~userThread, ~user, ~partner, kSending, rootKey, ~privateKey, 
                partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
                sndCtr, rcvCtr, prevRootKey, prevRcvChainKey)
    , Fr(~msgPayload) ]
    --[ SendsMessage(~userThread, ~user, ~partner, message, epochKey, sndCtr)
      , SendsMessage$1(~userThread, ~user, ~partner, message) 
      , ChainStep(~userThread, ~user, ~partner, epochKey, sndCtr, rcvCtr)
      , SendReceiveStep(~userThread, ~user, ~partner, epochKey, sndCtr)
      , Step(~userThread, ~user, ~partner)
      , SendPayload(~userThread, ~user, ~partner, ~msgPayload)
      , Neq(sndChainKey, kNullSndChainKey) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kSending, rootKey, 
                     ~privateKey, partnerPublicKey, rcvChainKey, $3, 
                     epochKey, $4, rcvCtr, prevRootKey, prevRcvChainKey)
    , Send(SendMessage$1, ~user, ~partner, <!<message, messageMAC>!>) ]

SendRule(SendMessage$1, ~sender, ~receiver)
!>)

SendMessageRule(Normal, dcffab, nextSndChainKey, sndCtr + '0')

ifelse(WITH_SINGLE_STATE_LOSS, true,
<!SendMessageRule(SingleStateLoss, f6c7fc, sndChainKey, sndCtr)!>,)

rule ReceiveStartKeyChain [color=6685ff]:
    let
        dhOut = newPartnerPublicKey^~privateKey
        nextRootKey = KDF(kFirst, dhOut, rootKey)
        newRcvChainKey = KDF(kSecond, dhOut, rootKey)
        nextRcvChainKey = KDF(kFirst, kMessageChain, newRcvChainKey)
        sndChainKey = KDF(kFirst, something, oldSndChainKey)
        messageKey = KDF(kSecond, kMessageChain, newRcvChainKey)
        message = <senc(msgPayload, messageKey), newPartnerPublicKey, rcvCtr+'0'>
    in
    [ UserState(~userThread, ~user, ~partner, kSending, rootKey, ~privateKey, 
                partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
                sndCtr, rcvCtr, prevRootKey, prevRcvChainKey)[no_precomp]
    , Receive(~user, ~partner, <!<message, messageMAC>!>) ]
    --[ StartReceiverKeyChain(~userThread, nextRootKey, ~privateKey, 
                              newPartnerPublicKey, nextRcvChainKey, sndChainKey)
      , StartKeyChain(~userThread, rootKey, ~privateKey, newPartnerPublicKey, 
                      nextRcvChainKey, sndChainKey)
      , ChainStep(~userThread, ~user, ~partner, epochKey, sndCtr, rcvCtr+'0')
      , SendReceiveStep(~userThread, ~user, ~partner, epochKey, sndCtr)
      , Step(~userThread, ~user, ~partner)
      , ReceivePayload(~userThread, ~user, ~partner, msgPayload)
      , ReceivesMessage(~userThread, ~user, ~partner, message, epochKey, rcvCtr+'0') 
      , Eq(messageMAC, MAC(message, epochKey)) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kReceiving, nextRootKey, 
                     ~privateKey, newPartnerPublicKey, 
                     nextRcvChainKey, sndChainKey, epochKey, 
                     sndCtr, rcvCtr+'0', rootKey, rcvChainKey) ]

rule ReceiveStartKeyChainAgain [color=6685ff]:
    let
        dhOut = newPartnerPublicKey^~privateKey
        nextRootKey = KDF(kFirst, dhOut, prevRootKey)
        newRcvChainKey = KDF(kSecond, dhOut, prevRootKey)
        nextRcvChainKey = KDF(kFirst, kMessageChain, newRcvChainKey)
        sndChainKey = KDF(kFirst, something, oldSndChainKey)
        messageKey = KDF(kSecond, kMessageChain, newRcvChainKey)
        message = <senc(msgPayload, messageKey), newPartnerPublicKey, rcvCtr>
        
    in
    [ UserState(~userThread, ~user, ~partner, kReceiving, rootKey, ~privateKey, 
                partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
                sndCtr, rcvCtr, prevRootKey, prevRcvChainKey)
    , Receive(~user, ~partner, <!<message, messageMAC>!>) ]
    --[ StartReceiverKeyChain(~userThread, nextRootKey, ~privateKey, 
                              newPartnerPublicKey, nextRcvChainKey, sndChainKey)
      , StartKeyChain(~userThread, rootKey, ~privateKey, newPartnerPublicKey, 
                         nextRcvChainKey, sndChainKey)
      , ReceivesMessage(~userThread, ~user, ~partner, message, epochKey, rcvCtr) 
      , ChainStep(~userThread, ~user, ~partner, epochKey, sndCtr, rcvCtr)
      , SendReceiveStep(~userThread, ~user, ~partner, epochKey, sndCtr)
      , Step(~userThread, ~user, ~partner)
      , ReceivePayload(~userThread, ~user, ~partner, msgPayload)
      , Eq(messageMAC, MAC(message, epochKey)) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kReceiving, nextRootKey, 
                     ~privateKey, newPartnerPublicKey, 
                     nextRcvChainKey, sndChainKey, epochKey, 
                     sndCtr, rcvCtr,
                     prevRootKey, prevRcvChainKey) ]

rule ReceiveMessage [color=c0ccfc]:
    let
        rootKey = KDF(kFirst, dhOut, rk)
        sndChainKey = KDF(kFirst, something, oldSndChainKey)
        nextRcvChainKey = KDF(kFirst, kMessageChain, rcvChainKey)
        messageKey = KDF(kSecond, kMessageChain, rcvChainKey)
        message = <senc(msgPayload, messageKey), partnerPublicKey, rcvCtr+'0'>
    in
    [ UserState(~userThread, ~user, ~partner, kReceiving, rootKey, ~privateKey, 
                partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
                sndCtr, rcvCtr, prevRootKey, prevRcvChainKey)
    , Receive(~user, ~partner, <!<message, messageMAC>!>) ] 
    --[ ReceivesMessage(~userThread, ~user, ~partner, message, epochKey, rcvCtr+'0') 
      , ChainStep(~userThread, ~user, ~partner, epochKey, sndCtr, rcvCtr+'0')
      , SendReceiveStep(~userThread, ~user, ~partner, epochKey, sndCtr)
      , Step(~userThread, ~user, ~partner)
      , ReceivePayload(~userThread, ~user, ~partner, msgPayload)
      , Eq(messageMAC, MAC(message, epochKey)) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kReceiving, rootKey, 
                     ~privateKey, partnerPublicKey, 
                     nextRcvChainKey, sndChainKey, epochKey, 
                     sndCtr, rcvCtr+'0', rootKey, rcvChainKey) ]

rule ReceiveMessageFromSingleStateLoss [color=c0ccfc]:
    let
        rootKey = KDF(kFirst, dhOut, rk)
        sndChainKey = KDF(kFirst, something, oldSndChainKey)
        nextRcvChainKey = KDF(kFirst, kMessageChain, prevRcvChainKey)
        messageKey = KDF(kSecond, kMessageChain, prevRcvChainKey)
        message = <senc(msgPayload, messageKey), partnerPublicKey, rcvCtr>
    in
    [ UserState(~userThread, ~user, ~partner, kReceiving, rootKey, ~privateKey, 
                partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
                sndCtr, rcvCtr, prevRootKey, prevRcvChainKey)
    , Receive(~user, ~partner, <!<message, messageMAC>!>) ] 
    --[ ReceivesMessage(~userThread, ~user, ~partner, message, epochKey, rcvCtr) 
      , ChainStep(~userThread, ~user, ~partner, epochKey, sndCtr, rcvCtr)
      , SendReceiveStep(~userThread, ~user, ~partner, epochKey, sndCtr)
      , Step(~userThread, ~user, ~partner)
      , ReceivePayload(~userThread, ~user, ~partner, msgPayload)
      , Eq(messageMAC, MAC(message, epochKey)) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kReceiving, rootKey, 
                    ~privateKey, partnerPublicKey, nextRcvChainKey, sndChainKey, 
                    epochKey, sndCtr, rcvCtr,
                    prevRootKey, prevRcvChainKey) ]

define(DetectCloneRule,
<!
rule ReceiveMessageDetectClone$1 [color=c596fa]:
    let
        rootKey = KDF(kFirst, dhOut, rk)
        dummyPartnerPublicKey = 'g'^~dummyPartnerPrivateKey
        rcvChainKey = KDF(kFirst, something, oldRcvChainKey)
        sndChainKey = KDF(kFirst, something, oldSndChainKey)
        currMessageKey = KDF(kSecond, kMessageChain, rcvChainKey)
        prevMessageKey = KDF(kSecond, kMessageChain, prevRcvChainKey)
        message = <senc(msgPayload, messageKey), inPartnerPublicKey, inRcvCtr>
    in
    [ UserState(~userThread, ~user, ~partner, state, rootKey, ~privateKey, 
                partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
                sndCtr, rcvCtr, prevRootKey, prevRcvChainKey)
    , Fr(~dummyPartnerPrivateKey)
    , Receive(~user, ~partner, <!<message, messageMAC>!>) ]
    --[ ReceivesMessage(~userThread, ~user, ~partner, message, epochKey, inRcvCtr)
      , ChainStep(~userThread, ~user, ~partner, epochKey, sndCtr, inRcvCtr)
      , Step(~userThread, ~user, ~partner)
      , ReceivePayload(~userThread, ~user, ~partner, msgPayload)
      , DetectClone(~userThread, ~user, ~partner, epochKey, inRcvCtr, messageMAC)
      , $2
      , Neq(state, kInitResponder)
      , Neq(state, kInitInitializer)
      , Neq(state, kInitializationStart) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kInitInitializer, rootKey, 
                     ~privateKey, dummyPartnerPublicKey, 
                     rcvChainKey, sndChainKey, epochKey, sndCtr, rcvCtr,
                     prevRootKey, prevRcvChainKey) ]
!>)

DetectCloneRule(InvalidMAC, 
<!InvalidMAC(messageMAC, MAC(message, epochKey))!>)

DetectCloneRule(MessageNumberTooLow,
<!Eq(messageMAC, MAC(message, epochKey)), 
  MessageNumberIsTooLow(rcvCtr, inRcvCtr)!>)

// END Double Ratchet with Single-State Loss and Clone Detection

// BEGIN Total-State Loss

ifelse(WITH_TOTAL_STATE_LOSS, true,
<!
rule TotalStateLoss [color=ff70ba]:
    let
        rootKey = KDF(kFirst, dhOut, rk)
        dummyEpochKey = h(kNullRootKey)
        dummyPartnerPublicKey = 'g'^~dummyPartnerPrivateKey
        rcvCtrZero = kZero
        sndCtrZero = kZero + '0'
    in
    [ UserState(~userThread, ~user, ~partner, state, rootKey, ~privateKey, 
                partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
                sndCtr, rcvCtr, prevRootKey, prevRcvChainKey)
    , Fr(~dummyPrivateKey)
    , Fr(~dummyPartnerPrivateKey) ]
    --[ TotalStateLoss(~userThread) 
      , Step(~userThread, ~user, ~partner)
      , Neq(state, kInitInitializer)
      , Neq(state, kInitResponder) ]->
    [ UserStateFacts(~userThread, ~user, ~partner, kInitInitializer, kNullRootKey, 
                     ~dummyPrivateKey, dummyPartnerPublicKey, kNullRcvChainKey, 
                     kNullSndChainKey, epochKey, sndCtrZero, rcvCtrZero, 
                     kNullRootKey, kNullRcvChainKey) ]
!>,)

// END Total-State Loss

// BEGIN State Compromise

rule StateCloneUser [color=aa0000]:
    [ UserData(~userThread, ~user, ~partner, state, rootKey, ~privateKey, 
               partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
               sndCtr, rcvCtr, prevRootKey, prevRcvChainKey)[no_precomp]
    , Fr(~attackerThread) ]
    --[ CloneUserThread(~userThread, ~attackerThread, ~user, ~partner)
      , CloneUser(~user, ~partner) ]->
    [ UserState(~attackerThread, ~user, ~partner, state, rootKey, ~privateKey, 
                partnerPublicKey, rcvChainKey, sndChainKey, epochKey, 
                sndCtr, rcvCtr, prevRootKey, prevRcvChainKey) ]

// END State Compromise

// BEGIN Sanity Statement

lemma can_receive_message [heuristic=S]: exists-trace
    "Ex receiverThread receiver sender message epochKey rcvCtr #i. 
     ReceivesMessage(receiverThread, receiver, sender, message, epochKey, rcvCtr) @ i"

// END Sanity Statement

// BEGIN Lemmas

lemma step_must_be_preceded_by_associate 
      [reuse, use_induction, heuristic=S]:
    "All senderThread sender receiver #i. 
    Step(senderThread, sender, receiver) @ i
    ==>
    (Ex #j. j < i & AssociateUsers(sender, receiver) @ j)"

lemma step_of_non_clone_must_be_preceded_by_start 
      [reuse, use_induction, heuristic=S]:
    "All senderThread sender receiver #i. 
    Step(senderThread, sender, receiver) @ i &
    (not Ex #j. j < i & CloneUser(sender, receiver) @ j) 
    ==>
    (Ex #j. j < i & StartChain(senderThread, sender, receiver) @ j)"

lemma send_of_non_clone_must_be_preceded_by_start 
      [reuse]:
    "All senderThread sender receiver msg epochKey sndCtr  #i. 
    SendsMessage(senderThread, sender, receiver, msg, epochKey, sndCtr) @ i &
    (not Ex #j. j < i & CloneUser(sender, receiver) @ j)
    ==>
    (Ex #j. j < i & StartChain(senderThread, sender, receiver) @ j)"

lemma steps_from_different_users_implies_user_was_cloned
      [reuse,
       hide_lemma=send_of_non_clone_must_be_preceded_by_start]:
    "All thread1 thread2 user partner #j1 #j2. 
    Step(thread1, user, partner)[-] @ j1 &
    Step(thread2, user, partner)[-] @ j2 &
    not TotalStateLoss(thread1) @ j1 &
    not TotalStateLoss(thread2) @ j2 &
    not thread1 = thread2
    ==>
    Ex #i. (i < j1 | i < j2) & CloneUser(user, partner) @ i"

lemma chain_step_of_non_clone_must_be_preceded_by_initialize 
      [reuse, use_induction, heuristic=S,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start]:
    "All userThread user partner epochKey sndCtr rcvCtr #i. 
      ChainStep(userThread, user, partner, epochKey, sndCtr, rcvCtr) @ i
    & not TotalStateLoss(userThread) @ i
    & (not Ex #j. (j < i) & CloneUser(user, partner) @ j)
    ==>
    (Ex #j. (#j = #i | j < i)
     & Initialized(userThread, user, partner, epochKey) @ j)"

lemma initialize_is_unique_for_epoch_key 
      [reuse, heuristic=S,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize]:
    "All user userThread partner epochKey #i #j.
     Initialized(userThread, user, partner, epochKey)[+] @ i &
     Initialized(userThread, user, partner, epochKey)[+] @ j
     ==> #i = #j"

lemma initialize_precedes_other_chain_step_for_epoch_key 
      [reuse, use_induction, heuristic=S,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start,
       hide_lemma=step_must_be_preceded_by_associate]:
    "All userThread user partner epochKey sndCtr rcvCtr #i #j. 
     Initialized(userThread, user, partner, epochKey) @ j
     & ChainStep(userThread, user, partner, epochKey, sndCtr, rcvCtr) @ i
     & (not Ex #j. (j < i) & CloneUser(user, partner) @ j)
     ==> (#i = #j | j < i)"

// Can be proved automatically: It is crucial to first use the induction 
// hypothesis, then solve the ChainStep, in all the remaining cases, first 
// solve the UserState stemming from the ChainStep.
lemma honest_user_must_have_current_epoch_key
     [reuse, use_induction, heuristic=S,
      hide_lemma=step_of_non_clone_must_be_preceded_by_associate,
      hide_lemma=step_of_non_clone_must_be_preceded_by_start,
      hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize]:
    "All user userThread partner epochKey1 epochKey2 epochKey3 sndCtr rcvCtr
     #i #j #k. i < j & j < k 
     & ChainStep(userThread, user, partner, epochKey3, sndCtr, rcvCtr)[+] @ k
     & StartInitialize(userThread, user, partner, epochKey1)[+] @ i
     & StartInitialize(userThread, user, partner, epochKey2)[+] @ j
     & not epochKey1 = epochKey2
     & (not Ex #l. (l < k) & CloneUser(user, partner) @ l)
     & (not Ex #l. (l < k) & CloneUser(partner, user) @ l)
     ==>
     not epochKey1 = epochKey3"

lemma chain_step_of_non_clone_must_be_preceded_by_unique_initialize 
      [reuse, heuristic=S,
       hide_lemma=step_must_be_preceded_by_associate,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start
       /*hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize*/]:
    "All userThread user partner epochKey sndCtr rcvCtr #i. 
      ChainStep(userThread, user, partner, epochKey, sndCtr, rcvCtr)[+] @ i
    & (not Ex #j. (j < i) & CloneUser(user, partner) @ j)
    & (not Ex #j. (j < i) & CloneUser(partner, user) @ j)
    ==>
    (Ex #j. (#j = #i | j < i)
     & Initialized(userThread, user, partner, epochKey) @ j 
     & not (Ex epochKeyK #k. j < k & k < i &
          Initialized(userThread, user, partner, epochKeyK) @ k))"

lemma sound_clone_detection_epoch_key 
     [reuse, heuristic=S,
      hide_lemma=step_must_be_preceded_by_associate,
      hide_lemma=step_of_non_clone_must_be_preceded_by_start,
      hide_lemma=send_of_non_clone_must_be_preceded_by_start,
      hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize/*,
      hide_lemma=honest_user_must_have_current_epoch_key*/]:
    "All userThread user partner epochKey inRcvCtr messageMAC #i.
     DetectClone(userThread, user, partner, epochKey, inRcvCtr, messageMAC)[+] @ i &
     (Ex validMAC. InvalidMAC(messageMAC, validMAC) @ i) &
     (not Ex #j. j < i & CloneUser(user, partner) @ j)
     ==> 
     Ex #j. j < i & CloneUser(partner, user) @ j"

lemma snd_nr_of_non_clone_increases_monotonically_for_epoch_key
      [reuse, use_induction, heuristic=S,
       hide_lemma=step_must_be_preceded_by_associate,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start,
       hide_lemma=send_of_non_clone_must_be_preceded_by_start,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_unique_initialize,
       hide_lemma=honest_user_must_have_current_epoch_key]:
    "All thread sender receiver sndCtr1 sndCtr2 rcvCtr1 rcvCtr2 epochKey #j1 #j2. 
    ChainStep(thread, sender, receiver, epochKey, sndCtr1, rcvCtr1)[+] @ j1 &
    ChainStep(thread, sender, receiver, epochKey, sndCtr2, rcvCtr2)[+] @ j2 & 
    (not Ex x y. MessageNumberIsTooLow(x, y) @ j1) & 
    (not Ex x y. MessageNumberIsTooLow(x, y) @ j2) & 
    j1 < j2 &
    (not Ex #i. i < j2 & CloneUser(sender, receiver) @ i)
    ==>
    (sndCtr1 = sndCtr2 | Ex x. sndCtr2 = sndCtr1 + x)"

lemma received_rcv_nr_from_non_clone_increases_monotonically_for_epoch_key
      [reuse, use_induction, heuristic=S,
       hide_lemma=step_must_be_preceded_by_associate,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start,
       hide_lemma=send_of_non_clone_must_be_preceded_by_start,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_unique_initialize,
       hide_lemma=honest_user_must_have_current_epoch_key]:
    "All thread sender receiver msg1 msg2 rcvCtr1 rcvCtr2 epochKey #j1 #j2. 
    ReceivesMessage(thread, receiver, sender, msg1, epochKey, rcvCtr1)[+] @ j1 &
    ReceivesMessage(thread, receiver, sender, msg2, epochKey, rcvCtr2)[+] @ j2 & 
    j1 < j2 &
    (not Ex #i. i < j2 & CloneUser(sender, receiver) @ i) &
    (not Ex #i. i < j2 & CloneUser(receiver, sender) @ i)
    ==>
    (rcvCtr1 = rcvCtr2 | Ex x. rcvCtr2 = rcvCtr1 + x)"

lemma chain_step_precedes_detect_clone_for_epoch_key
      [reuse, use_induction, heuristic=S,
       hide_lemma=step_must_be_preceded_by_associate,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start,
       hide_lemma=send_of_non_clone_must_be_preceded_by_start,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_unique_initialize,
       hide_lemma=honest_user_must_have_current_epoch_key,
       hide_lemma=snd_nr_of_non_clone_increases_monotonically_for_epoch_key,
       hide_lemma=received_rcv_nr_from_non_clone_increases_monotonically_for_epoch_key]:
    "All senderThread sender receiver epochKey sndCtr rcvCtr number messageMAC 
     #i #j. 
    ChainStep(senderThread, sender, receiver, epochKey, sndCtr, rcvCtr)[+] @ i &
    DetectClone(senderThread, sender, receiver, epochKey, number, messageMAC)[+] @ j &
    (not Ex #k. (k < i | k < j) & CloneUser(sender, receiver) @ k) &
    (not Ex #k. (k < i | k < j) & CloneUser(receiver, sender) @ k)
    ==>
    (#i = #j | i < j)"

lemma non_zero_rcv_nr_must_have_been_received
      [reuse, use_induction, heuristic=S,
       hide_lemma=step_must_be_preceded_by_associate,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start,
       hide_lemma=send_of_non_clone_must_be_preceded_by_start,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_unique_initialize,
       hide_lemma=honest_user_must_have_current_epoch_key]:
    "All thread sender receiver sndCtr rcvCtr epochKey #j. 
    ChainStep(thread, receiver, sender, epochKey, sndCtr, rcvCtr)[+] @ j &
    not rcvCtr = kZero &
    (not Ex #i. i < j & CloneUser(sender, receiver) @ i) &
    (not Ex #i. i < j & CloneUser(receiver, sender) @ i)
    ==>
    Ex msg #i. (#i = #j | i < j) &
    ReceivesMessage(thread, receiver, sender, msg, epochKey, rcvCtr)[+] @ i"

lemma rcv_nr_from_non_clone_increases_monotonically_for_epoch_key_at_detect
      [reuse, use_induction, heuristic=S,
       hide_lemma=step_must_be_preceded_by_associate,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start,
       hide_lemma=send_of_non_clone_must_be_preceded_by_start,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_unique_initialize,
       hide_lemma=honest_user_must_have_current_epoch_key,
       hide_lemma=snd_nr_of_non_clone_increases_monotonically_for_epoch_key]:
    "All thread sender receiver sndCtr1 rcvCtr1 rcvCtr2 epochKey messageMAC #j1 #j2. 
    DetectClone(thread, receiver, sender, epochKey, rcvCtr2, messageMAC)[+] @ j2 & 
    ChainStep(thread, receiver, sender, epochKey, sndCtr1, rcvCtr1) @ j1 &
    j1 < j2 &
    (not Ex #i. i < j2 & CloneUser(sender, receiver) @ i) &
    (not Ex #i. i < j2 & CloneUser(receiver, sender) @ i)
    ==>
    (rcvCtr1 = rcvCtr2 | Ex x. rcvCtr2 = rcvCtr1 + x)"

lemma rcv_nr_from_non_clone_increases_monotonically_for_epoch_key
      [reuse, use_induction, heuristic=S,
       hide_lemma=step_must_be_preceded_by_associate,
       hide_lemma=step_of_non_clone_must_be_preceded_by_start,
       hide_lemma=send_of_non_clone_must_be_preceded_by_start,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize,
       hide_lemma=chain_step_of_non_clone_must_be_preceded_by_unique_initialize,
       hide_lemma=honest_user_must_have_current_epoch_key,
       hide_lemma=snd_nr_of_non_clone_increases_monotonically_for_epoch_key,
       hide_lemma=non_zero_rcv_nr_must_have_been_received]:
    "All thread sender receiver sndCtr1 sndCtr2 rcvCtr1 rcvCtr2 epochKey #j1 #j2. 
    ChainStep(thread, receiver, sender, epochKey, sndCtr2, rcvCtr2)[+] @ j2 & 
    ChainStep(thread, receiver, sender, epochKey, sndCtr1, rcvCtr1)[+] @ j1 &
    j1 < j2 &
    (not Ex #i. i < j2 & CloneUser(sender, receiver) @ i) &
    (not Ex #i. i < j2 & CloneUser(receiver, sender) @ i)
    ==>
    (rcvCtr1 = rcvCtr2 | Ex x. rcvCtr2 = rcvCtr1 + x)"

lemma messages_from_different_senders_implies_user_was_cloned
      [reuse]:
    "All thread1 thread2 sender receiver m1 m2 sndCtr1 sndCtr2 
     epochKey1 epochKey2 #j1 #j2. 
    SendsMessage(thread1, sender, receiver, m1, epochKey1, sndCtr1)[-] @ j1 &
    SendsMessage(thread2, sender, receiver, m2, epochKey2, sndCtr2)[-] @ j2 & 
    not thread1 = thread2
    ==>
    Ex #i. (i < j1 | i < j2) & CloneUser(sender, receiver) @ i"

lemma sound_clone_detection_message_number [reuse,heuristic=S,
     hide_lemma=step_must_be_preceded_by_associate,
     hide_lemma=step_of_non_clone_must_be_preceded_by_start,
     hide_lemma=send_of_non_clone_must_be_preceded_by_start,
     hide_lemma=honest_user_must_have_current_epoch_key,
     hide_lemma=chain_step_of_non_clone_must_be_preceded_by_initialize,
     hide_lemma=chain_step_of_non_clone_must_be_preceded_by_unique_initialize]:
    "All userThread user partner epochKey inRcvCtr messageMAC #i.
     DetectClone(userThread, user, partner, epochKey, inRcvCtr, messageMAC) @ i &
     not (Ex validMAC. InvalidMAC(messageMAC, validMAC) @ i)
     & (not Ex #j. j < i & CloneUser(user, partner) @ j)
     ==> 
     Ex #j. j < i & CloneUser(partner, user) @ j"

// BEGIN Main Statement

lemma sound_clone_detection
    [heuristic=S,
     hide_lemma=chain_step_of_non_clone_must_be_preceded_by_association,
     hide_lemma=send_of_non_clone_must_be_preceded_by_association,
     hide_lemma=messages_from_different_senders_implies_user_was_cloned,
     hide_lemma=detect_clone_implies_receives_from_different_senders,
     hide_lemma=detect_clone_implies_sends_from_different_senders]:
    "All userThread user partner epochKey inRcvCtr messageMAC #i.
    DetectClone(userThread, user, partner, epochKey, inRcvCtr, messageMAC) @ i &
    (not Ex #j. j < i & CloneUser(user, partner) @ j)
    ==>
    Ex #j. j < i & CloneUser(partner, user) @ j"

// END Main Statement

// END Lemmas

end

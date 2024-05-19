module ElectronicLockSystem

open util/boolean

sig Server {
    sendCode: set Int -> set Int,
    successResponse: set Int
}

sig RFIDReader {
    cardRead: lone Int,
    serverResponse: lone Int
}

sig ElectricMagnet {
    isLocked: one Bool
}

sig ElectronicLock {
    connectedToServer: lone Server,
    connectedToRFIDReader: lone RFIDReader,
    electricMagnet: one ElectricMagnet,
    isInitialized: one Bool
}

pred initializeSystem(l: ElectronicLock, r: RFIDReader) {
    l.connectedToServer in Server and
    l.connectedToRFIDReader = r and
    l.electricMagnet.isLocked = True and
    l.isInitialized = True and
    r.cardRead = none and
    r.serverResponse = none
}

pred openMagnet(l: ElectronicLock, r: RFIDReader, time: Int) {
    some c: r.cardRead |
    ((c = 1 or c = 2 or c = 3 or c = 4 or c = 5) and l.connectedToRFIDReader = r) or
    ((l.connectedToRFIDReader = r and l.connectedToServer.sendCode[c] = r.serverResponse) =>
        l.electricMagnet.isLocked = False and
        l.isInitialized = True and
        time >= 0 and time <= 10)
}

fact MagnetBehavior {
    all l: ElectronicLock, r: RFIDReader | 
        (openMagnet[l, r, 10] implies 
         (r.cardRead = 1 or r.cardRead = 2 or r.cardRead = 3 or r.cardRead = 4 or r.cardRead = 5) or
         (r.serverResponse in l.connectedToServer.successResponse))
}

run {
    some l: ElectronicLock, r: RFIDReader | initializeSystem[l, r]
} for 3 but exactly 1 Server, 1 RFIDReader, 1 ElectricMagnet, 1 ElectronicLock


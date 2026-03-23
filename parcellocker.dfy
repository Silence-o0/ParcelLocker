datatype Size = Small | Medium | Large

predicate Fits(item: Size, locker: Size)
{
  match item
  case Small  => true
  case Medium => locker == Medium || locker == Large
  case Large  => locker == Large
}

lemma FitsReflexive(s: Size)
  ensures Fits(s, s)
{}

class Locker {
  var occupied: bool
  var parcelId: int
  var receiverId: int
  const size: Size

  ghost predicate Valid()
    reads this
  {
    (occupied  ==> parcelId > 0 && receiverId > 0) &&
    (!occupied ==> parcelId == -1 && receiverId == -1)
  }

  constructor(s: Size)
    ensures size == s
    ensures !occupied
    ensures parcelId == -1
    ensures receiverId == -1
    ensures Valid()
  {
    size := s;
    occupied := false;
    parcelId := -1;
    receiverId := -1;
  }

  method PlaceParcel(id: int, receiver: int, parcelSize: Size)
    requires Valid()
    requires !occupied
    requires id > 0
    requires receiver > 0
    requires Fits(parcelSize, size)
    modifies this
    ensures occupied
    ensures parcelId == id
    ensures receiverId == receiver
    ensures Valid()
  {
    occupied := true;
    parcelId := id;
    receiverId := receiver;
  }

  method RemoveParcel(userId: int, isCourier: bool)
    requires Valid()
    requires occupied
    requires userId == receiverId || isCourier
    modifies this
    ensures !occupied
    ensures parcelId == -1
    ensures receiverId == -1
    ensures Valid()
  {
    occupied := false;
    parcelId := -1;
    receiverId := -1;
  }
}

class ParcelLocker {
  var lockers: array<Locker>

  ghost predicate Valid()
    reads this, lockers,
          set i | 0 <= i < lockers.Length :: lockers[i]
  {
    lockers.Length > 0 &&

    (forall i :: 0 <= i < lockers.Length ==>
      lockers[i].Valid()) &&

    forall i, j :: 0 <= i < j < lockers.Length &&
                   lockers[i].occupied &&
                   lockers[j].occupied
                ==> lockers[i].parcelId != lockers[j].parcelId
  }

  ghost predicate HasFreeForSize(s: Size)
    requires Valid()
    reads this, lockers,
          set i | 0 <= i < lockers.Length :: lockers[i]
  {
    exists i :: 0 <= i < lockers.Length &&
                !lockers[i].occupied &&
                Fits(s, lockers[i].size)
  }

  ghost predicate AllOccupied()
    requires Valid()
    reads this, lockers,
          set i | 0 <= i < lockers.Length :: lockers[i]
  {
    forall i :: 0 <= i < lockers.Length ==>
                lockers[i].occupied
  }

  lemma AllOccupiedForAnySize()
    requires Valid()
    requires AllOccupied()
    ensures forall s: Size :: !HasFreeForSize(s)
  {}
}
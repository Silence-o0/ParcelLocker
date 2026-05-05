datatype PowerState = MainPower | BackupPower

class Locker {
  var doorOpen: bool
  var locked: bool
  const widthCm: nat
  const heightCm: nat
  const depthCm: nat

  ghost predicate Valid()
    reads this
  {
    doorOpen ==> !locked
  }

  constructor (w: nat, h: nat, d: nat)
    ensures widthCm == w && heightCm == h && depthCm == d
    ensures !doorOpen && locked
    ensures Valid()
  {
    widthCm := w;
    heightCm := h;
    depthCm := d;
    doorOpen := false;
    locked := true;
  }

  function Fits(w: nat, h: nat, d: nat): bool
    reads this
  {
    w <= widthCm && h <= heightCm && d <= depthCm
  }

  method Unlock()
    requires Valid() && locked && !doorOpen
    modifies this
    ensures !locked && !doorOpen
    ensures Valid()
  {
    locked := false;
  }

  method Lock()
    requires Valid() && !locked && !doorOpen
    modifies this
    ensures locked && !doorOpen
    ensures Valid()
  {
    locked := true;
  }

  method OpenDoor()
    requires Valid() && !locked && !doorOpen
    modifies this
    ensures doorOpen && !locked
    ensures Valid()
  {
    doorOpen := true;
  }

  method CloseDoor()
    requires Valid() && doorOpen && !locked
    modifies this
    ensures !doorOpen && !locked
    ensures Valid()
  {
    doorOpen := false;
  }
}

class ParcelLocker {
  const lockers: seq<Locker>
  var power: PowerState
  var poweredOn: bool

  ghost predicate Valid()
    reads this, set c | c in lockers
  {
    forall i :: 0 <= i < |lockers| ==> lockers[i].Valid()
  }

  constructor (obj: seq<Locker>)
    requires forall i :: 0 <= i < |obj| ==> obj[i].Valid()
    ensures lockers == obj
    ensures power == MainPower && poweredOn
    ensures Valid()
  {
    lockers := obj;
    power := MainPower;
    poweredOn := true;
  }

  method SwitchToBackup()
    requires poweredOn && power == MainPower
    modifies this
    ensures poweredOn && power == BackupPower
  {
    power := BackupPower;
  }

  method SwitchToMain()
    requires poweredOn && power == BackupPower
    modifies this
    ensures poweredOn && power == MainPower
  {
    power := MainPower;
  }

  method PowerOff()
    requires poweredOn
    modifies this
    ensures !poweredOn
    ensures power == old(power)
  {
    poweredOn := false;
  }

  method PowerOn()
    requires !poweredOn
    modifies this
    ensures poweredOn
    ensures power == old(power)
  {
    poweredOn := true;
  }

  method UnlockLocker(i: int)
    requires Valid()
    requires 0 <= i < |lockers|
    requires poweredOn
    requires lockers[i].locked && !lockers[i].doorOpen
    modifies lockers[i]
    ensures !lockers[i].locked && !lockers[i].doorOpen
    ensures Valid()
  {
    lockers[i].Unlock();
  }

  method LockLocker(i: int)
    requires Valid()
    requires 0 <= i < |lockers|
    requires poweredOn
    requires !lockers[i].locked && !lockers[i].doorOpen
    modifies lockers[i]
    ensures lockers[i].locked && !lockers[i].doorOpen
    ensures Valid()
  {
    lockers[i].Lock();
  }

  method OpenLockerDoor(i: int)
    requires Valid()
    requires 0 <= i < |lockers|
    requires !lockers[i].locked && !lockers[i].doorOpen
    modifies lockers[i]
    ensures lockers[i].doorOpen && !lockers[i].locked
    ensures Valid()
  {
    lockers[i].OpenDoor();
  }

  method CloseLockerDoor(i: int)
    requires Valid()
    requires 0 <= i < |lockers|
    requires lockers[i].doorOpen && !lockers[i].locked
    modifies lockers[i]
    ensures !lockers[i].doorOpen && !lockers[i].locked
    ensures Valid()
  {
    lockers[i].CloseDoor();
  }
}

method Main()
{
  var l0 := new Locker(40, 30, 50);
  var l1 := new Locker(60, 40, 60);
  var l2 := new Locker(20, 20, 30);

  assert l0.Fits(30, 20, 40);
  assert !l2.Fits(50, 50, 50);

  var parcellocker := new ParcelLocker([l0, l1, l2]);

  parcellocker.SwitchToBackup();
  parcellocker.SwitchToMain();

  parcellocker.UnlockLocker(0);
  parcellocker.OpenLockerDoor(0);
  parcellocker.CloseLockerDoor(0);
  parcellocker.LockLocker(0);

  parcellocker.PowerOff();
  parcellocker.PowerOn();

  parcellocker.UnlockLocker(1);
  parcellocker.OpenLockerDoor(1);
  parcellocker.CloseLockerDoor(1);
  parcellocker.LockLocker(1);

  print "ParcelLocker successfully executed";
}
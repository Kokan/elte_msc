class AbstractFamily {
  class AbstractHusband { };
  class AbstractWife { };
};

class Family extends AbstractFamily{
   class YoungHusband extends AbstractHusband { };
   class YoungWife    extends AbstractWife { };
};

class FamilyWithKids extends AbstractFamily {
  class Father extends AbstractHusband { def has_child(): Boolean = true; }; 
  class Mother extends AbstractWife { def has_child(): Boolean = true; };
};

class Room {
  def assign_husband(h: AbstractFamily#AbstractHusband): Room = this;
  def assign_wife(w: AbstractFamily#AbstractWife): Room = this;
};


val family = new Family();
val husband = new family.YoungHusband();
val wife = new family.YoungWife();

val room42 = new Room;
val room43 = new Room;

room42.assign_husband(husband);
room42.assign_wife(wife);

val marriedfamily = new FamilyWithKids();
val alsohusband = new marriedfamily.Father();
val alsowife = new marriedfamily.Mother();

assert(alsohusband.has_child);
// This would not compile as the husbend
// is just Husband end not a Father
//assert(husband.has_child); 

room43.assign_husband(alsohusband);
room43.assign_wife(alsowife);

room42.assign_husband(alsohusband);
room42.assign_wife(wife);

room42.assign_husband(husband);
room42.assign_wife(alsowife);


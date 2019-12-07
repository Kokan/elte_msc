class AbstractFamily {
  type Husband <: AbstractHusband
  type Wife    <: AbstractWife

  class AbstractHusband { };
  class AbstractWife { };
};

class Family extends AbstractFamily{
   type Husband = YoungHusband
   type Wife    = YoungWife

   class YoungHusband extends AbstractHusband { };
   class YoungWife    extends AbstractWife { };
};

class FamilyWithKids extends AbstractFamily {
  type Husband = Father
  type Wife    = Mother

  class Father extends AbstractHusband { def has_child(): Boolean = true; }; 
  class Mother extends AbstractWife { def has_child(): Boolean = true; };
};

abstract class Room {
  type F <: AbstractFamily

  private var husband: F#Husband = null.asInstanceOf[F#Husband]
  private var wife: F#Wife = null.asInstanceOf[F#Wife]

  def assign_husband(h: F#Husband): Room = { husband = h; this; }
  def assign_wife(w: F#Wife): Room = { wife = w; this; }
};


val family = new Family();
val family2 = new Family();
val husband = new family.Husband();
val wife = new family.Wife();
val husband2 = new family2.Husband();
val wife2 = new family2.Wife();

val room42 = new Room { type F = Family; };
val room43 = new Room { type F = FamilyWithKids; };

room42.assign_husband(husband);
room42.assign_wife(wife);

room42.assign_husband(husband2);

val marriedfamily = new FamilyWithKids();
val alsohusband = new marriedfamily.Husband();
val alsowife = new marriedfamily.Wife();

assert(alsohusband.has_child);
// This would not compile as the husbend
// is just Husband end not a Father
//assert(husband.has_child); 

room43.assign_husband(alsohusband);
room43.assign_wife(alsowife);

//room43.assign_wife(wife);

// The following examples should and does not compile
// family.scala:56: error: type mismatch;
//  found   : this.marriedfamily.Father
//  required: this.room42.F#Husband
//     (which expands to)  this.Family#YoungHusband
// room42.assign_husband(alsohusband);
//                       ^
// family.scala:60: error: type mismatch;
//  found   : this.marriedfamily.Mother
//  required: this.room42.F#Wife
//     (which expands to)  this.Family#YoungWife
// room42.assign_wife(alsowife);
//                    ^

//room42.assign_husband(alsohusband);
//room42.assign_wife(wife);
//
//room42.assign_husband(husband);
//room42.assign_wife(alsowife);


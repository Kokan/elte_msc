class Husband { };

class Father extends Husband { def has_child(): Boolean = true; }; 

class Wife { };
class Mother extends Wife { def has_child(): Boolean = true;};

class Room {
  def assign_husband(h: Husband) : Room = this;
  def assign_wife(w: Wife) : Room = this;
};


val husband = new Husband();
val wife = new Wife();

val room42 = new Room();
val room43 = new Room();

room42.assign_husband(husband);
room42.assign_wife(wife);

val alsohusband = new Father();
val alsowife = new Mother();

assert(alsohusband.has_child);
//assert(husband.has_child); // This would not compile as the husbend is just Husband end not a Father

room42.assign_husband(alsohusband);
room42.assign_wife(wife);

room43.assign_husband(husband);
room43.assign_wife(alsowife);


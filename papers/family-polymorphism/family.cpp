
template<typename W, typename H>
struct AbstractWife { int num_child() { return 0; } };

template<typename W, typename H>
struct AbstractHusband { };

struct Wife;
struct Husband : public AbstractHusband<Husband, Wife> {};
struct Wife : public AbstractWife<Husband, Wife> { };

struct Mother;
struct Father : public AbstractHusband<Father, Mother> { };
struct Mother : public AbstractWife<Father, Mother> {
  int number_of_child;
  int num_child() { return number_of_child; }
};

template <typename H, typename W> struct Room {
  W *wife;
  void assign(H *h, W *m) { wife = m; }
  int room_size() { return  wife->num_child(); };
};

int main() {
  auto *room42 = new Room<Husband, Wife>();
  auto *room43 = new Room<Father, Mother>();

  room42->assign(new Husband(), new Wife());
  //room42->assign(new Husband(), new Mother());
  room42->room_size();

  room43->assign(new Father(), new Mother());
  //room43->assign(new Husband(), new Mother());
  room43->room_size();

  return 0;
};

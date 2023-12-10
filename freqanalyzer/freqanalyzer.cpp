/* Lama SM Bytecode interpreter */

#include <algorithm>
#include <cerrno>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <stack>
#include <string>
#include <unordered_map>
#include <utility>

namespace {
class Logger {
private:
  Logger(std::ostream &o) : o(&o) {}
  Logger() = default;

  std::ostream *o = nullptr;

  static Logger instance;

  template <typename... ArgTs> Logger &log_(ArgTs &&...args) {
    if (o) {
      using expander = int[];
      (void)expander{0, (void(*o << std::forward<ArgTs>(args)), 0)...};
    }
    return *this;
  }

public:
  template <typename... ArgTs> static Logger &log(ArgTs &&...args) {
    return instance.log_(std::forward<ArgTs>(args)...);
  }
};

Logger Logger::instance(std::cout);

void failure(const char *s, ...) {
  va_list args;
  va_start(args, s);
  fprintf(stderr, "*** FAILURE: ");
  vfprintf(stderr, s, args);
  exit(255);
}

/* The unpacked representation of bytecode file */
struct bytefile {
  char *string_ptr;     /* A pointer to the beginning of the string table */
  int *public_ptr;      /* A pointer to the beginning of publics table    */
  char *code_ptr;       /* A pointer to the bytecode itself               */
  int stringtab_size;   /* The size (in bytes) of the string table        */
  int global_area_size; /* The size (in words) of global area             */
  int public_symbols_number; /* The number of public symbols */
  char buffer[0];

  bytefile(FILE *f, long size) {
    if (fread(&stringtab_size, sizeof(stringtab_size), 1, f) != 1 ||
        fread(&global_area_size, sizeof(stringtab_size), 1, f) != 1 ||
        fread(&public_symbols_number, sizeof(stringtab_size), 1, f) != 1)
      failure("%s\n", strerror(errno));

    size -= sizeof(int) * 3;

    if (size != fread(buffer, 1, size, f))
      failure("%s\n", strerror(errno));

    string_ptr = &buffer[public_symbols_number * 2 * sizeof(int)];
    public_ptr = (int *)buffer;
    code_ptr = &string_ptr[stringtab_size];
  }

  /* Gets a string from a string table by an index */
  const char *get_string(int pos) const { return &string_ptr[pos]; }

  /* Gets a name for a public symbol */
  const char *get_public_name(int i) const {
    return get_string(public_ptr[i * 2]);
  }

  /* Gets an offset for a public symbol */
  int get_public_offset(int i) const { return public_ptr[i * 2 + 1]; }

  static void deleter(bytefile *p) {
    p->~bytefile();
    operator delete(p);
  }
};

using bytefile_ptr = std::unique_ptr<bytefile, void (*)(bytefile *)>;

/* Reads a binary bytecode file by name and unpacks it */
bytefile_ptr read_file(char *fname) {
  FILE *f = fopen(fname, "rb");

  if (f == 0) {
    failure("%s\n", strerror(errno));
  }

  if (fseek(f, 0, SEEK_END) == -1) {
    failure("%s\n", strerror(errno));
  }

  long size = ftell(f);
  bytefile *file =
      (bytefile *)operator new(sizeof(bytefile) - 3 * sizeof(int) + size);
  rewind(f);
  new (file) bytefile(f, size);
  fclose(f);

  return bytefile_ptr(file, bytefile::deleter);
}

/* Bytecode enums */
namespace BC_H {
enum BC_H {
  BC_H_MIN = 0,
  BC_H_BINOP = BC_H_MIN,
  BC_H_STRAIGHT,
  BC_H_LD,
  BC_H_LDA,
  BC_H_ST,
  BC_H_CONTROL,
  BC_H_PATT,
  BC_H_CALL,
  BC_H_STOP = 15,
  BC_H_MAX = BC_H_STOP
};
}

namespace BC_L_BINOP {
enum BC_L_BINOP {
  BC_L_MIN = 1,
  BC_L_ADD = BC_L_MIN,
  BC_L_SUB,
  BC_L_MUL,
  BC_L_DIV,
  BC_L_MOD,
  BC_L_LT,
  BC_L_LTE,
  BC_L_GT,
  BC_L_GTE,
  BC_L_EQ,
  BC_L_NEQ,
  BC_L_AND,
  BC_L_OR,
  BC_L_MAX = BC_L_OR,
};
}

namespace BC_L_STRAIGHT {
enum BC_L_STRAIGHT {
  BC_L_MIN = 0,
  BC_L_CONST = BC_L_MIN,
  BC_L_STRING,
  BC_L_SEXP,
  BC_L_STI,
  BC_L_STA,
  BC_L_JMP,
  BC_L_END,
  BC_L_RET,
  BC_L_DROP,
  BC_L_DUP,
  BC_L_SWAP,
  BC_L_ELEM,
  BC_L_MAX = BC_L_ELEM,
};
}

namespace BC_L_LDS {
enum BC_L_LDS {
  BC_L_MIN = 0,
  BC_L_G = BC_L_MIN,
  BC_L_L,
  BC_L_A,
  BC_L_C,
  BC_L_MAX = BC_L_C
};
}

namespace BC_L_CONTROL {
enum BC_L_CONTROL {
  BC_L_MIN = 0,
  BC_L_CJMPz = BC_L_MIN,
  BC_L_CJMPnz,
  BC_L_BEGIN,
  BC_L_CBEGIN,
  BC_L_CLOSURE,
  BC_L_CALLC,
  BC_L_CALL,
  BC_L_TAG,
  BC_L_ARRAY,
  BC_L_FAIL,
  BC_L_LINE,
  BC_L_MAX = BC_L_LINE,
};
}

namespace BC_L_CALL_RUNTIME {
enum BC_L_CALL_RUNTIME {
  BC_L_MIN = 0,
  BC_L_READ = BC_L_MIN,
  BC_L_WRITE,
  BC_L_LENGTH,
  BC_L_STRING,
  BC_L_ARRAY,
  BC_L_MAX = BC_L_ARRAY,
};
}

namespace BC_L_PATT {
enum BC_L_PATT {
  BC_L_MIN = 0,
  BC_L_EQ_STR = BC_L_MIN,
  BC_L_STRING,
  BC_L_ARRAY,
  BC_L_SEXP,
  BC_L_BOX,
  BC_L_VAL,
  BC_L_FUN,
  BC_L_MAX = BC_L_FUN,
};
}

namespace BC_L_STOP {
enum BC_L_STOP {
  BC_L_MIN = 15,
  BC_L_STP = BC_L_MIN,
  BC_L_MAX = BC_L_STP,
};
}

template <auto val, typename U> struct DepTypePoint {
  using FromT = decltype(val);
  using ToT = U;
  template <typename ArgT> static constexpr bool matches(ArgT other_val) {
    if constexpr (std::is_same_v<ArgT, FromT>) {
      return val == other_val;
    }
    return false;
  }
};

template <typename... DepTypePoints> struct DependentType {
  template <auto val> using ToT = void;
  template <auto val> using ToPointT = void;
};

template <typename DepTypePoint, typename... DepTypePoints>
struct DependentType<DepTypePoint, DepTypePoints...>
    : DependentType<DepTypePoints...> {
  using PointT = DepTypePoint;
  using BaseT = DependentType<DepTypePoints...>;

  template <auto val>
  using Matches = std::bool_constant<DepTypePoint::matches(val)>;

  template <auto val>
  using ToPointT = std::conditional_t<
      Matches<val>::value, DepTypePoint,
      typename DependentType<DepTypePoints...>::template ToPointT<val>>;

  template <auto val>
  using ToT = std::conditional_t<
      Matches<val>::value, typename DepTypePoint::ToT,
      typename DependentType<DepTypePoints...>::template ToT<val>>;
};

template <char... str> struct StringDisplay_d {
  static constexpr inline char string[] = {str..., '\0'};

  static void print() { Logger::log(string); }
};

template <typename CharT, CharT... str> constexpr auto operator"" _d() {
  return StringDisplay_d<str...>::string;
}

constexpr std::pair<char, char> to_nibbles(char inst) {
  return {(inst & 0xF0) >> 4, inst & 0x0F};
}

constexpr char from_nibbles(char h, char l) { return (h << 4) | l; }

struct InstCapture {
  char h, l;
  InstCapture() = default;
  InstCapture(char h, char l) : h(h), l(l) {}

  template <typename ReaderT> static InstCapture read(ReaderT &ana) {
    return ana.template read<InstCapture>();
  }

  friend std::ostream &operator<<(std::ostream &o, const InstCapture &c) {
    return o;
  }

  friend bool operator==(const InstCapture &, const InstCapture &) {
    return true;
  }

  friend bool operator!=(const InstCapture &, const InstCapture &) {
    return false;
  }
};

struct BinopCapture : InstCapture {
  static inline constexpr const char *ops[13] = {
      "+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};

  template <typename ReaderT> static BinopCapture read(ReaderT &ana) {
    return {InstCapture::read(ana)};
  }

  friend std::ostream &operator<<(std::ostream &o, const BinopCapture &c) {
    return o << ops[c.l - 1];
  }
};

struct PattCapture : InstCapture {
  static inline constexpr const char *pats[7] = {
      "=str", "#string", "#array", "#sexp", "#box", "#val", "#fun"};

  template <typename ReaderT> static PattCapture read(ReaderT &ana) {
    return {InstCapture::read(ana)};
  }

  friend std::ostream &operator<<(std::ostream &o, const PattCapture &c) {
    return o << pats[c.l];
  }
};

struct CallCapture : InstCapture {
  static inline constexpr const char *funs[5] = {"Lread", "Lwrite", "Llength",
                                                 "Lstring", "Barray"};

  template <typename ReaderT> static CallCapture read(ReaderT &ana) {
    return {InstCapture::read(ana)};
  }

  friend std::ostream &operator<<(std::ostream &o, const CallCapture &c) {
    return o << funs[c.l];
  }
};

template <typename T> std::ostream &print_arg(std::ostream &o, T val) {
  return o << val;
}

template <> std::ostream &print_arg(std::ostream &o, void *val) {
  return o << "0x" << std::setw(8) << std::setfill('0') << std::hex << (int)val
           << std::dec;
}

template <typename... Ts> struct ArgCapture {
  using ArgT =
      std::conditional_t<sizeof...(Ts) == 1,
                         std::tuple_element_t<0, std::tuple<Ts..., int>>,
                         std::tuple<Ts...>>;
  ArgT val;

  template <typename ReaderT, size_t... I>
  static ArgCapture read_i(ArgT &val, ReaderT &ana, std::index_sequence<I...>) {
    ((std::get<I>(val) = ana.template read<std::tuple_element_t<I, ArgT>>()),
     ...);
    return ArgCapture{val};
  }

  template <typename ReaderT> static ArgCapture read(ReaderT &ana) {
    if constexpr (sizeof...(Ts) == 1) {
      return ArgCapture{ana.template read<Ts>()...};
    } else {
      ArgT val;
      return read_i(val, ana, std::make_index_sequence<sizeof...(Ts)>());
    }
  }

  template <size_t... I>
  std::ostream &print_i(std::ostream &o, std::index_sequence<I...>) const {
    ((print_arg(o, std::get<I>(val)) << ' '), ...);
    return o;
  }

  friend std::ostream &operator<<(std::ostream &o, const ArgCapture &c) {
    if constexpr (sizeof...(Ts) == 1) {
      return print_arg(o, c.val);
    } else {
      return c.print_i(o, std::make_index_sequence<sizeof...(Ts)>());
    }
  }

  template <size_t... I>
  size_t hash_i(size_t seed, std::index_sequence<I...>) const {
    ((seed ^= std::hash<std::tuple_element_t<I, ArgT>>{}(std::get<I>(val)) +
              0x9e3779b9 + (seed << 6) + (seed >> 2)),
     ...);
    return seed;
  }

  bool operator==(const ArgCapture &c) const { return val == c.val; }

  bool operator!=(const ArgCapture &c) const { return !operator==(c); }
};

struct VarCapture : InstCapture, ArgCapture<int> {
  static inline constexpr const char *tags[4] = {"G", "L", "A", "C"};

  template <typename ReaderT> static VarCapture read(ReaderT &ana) {
    return {InstCapture::read(ana), ArgCapture<int>::read(ana)};
  }

  friend std::ostream &operator<<(std::ostream &o, const VarCapture &c) {
    return o << tags[c.l] << '(' << c.val << ')';
  }

  bool operator==(const VarCapture &c) const {
    return static_cast<const ArgCapture<int> &>(*this) == c;
  }

  bool operator!=(const VarCapture &c) const { return !operator==(c); }
};
} // namespace

namespace std {
template <typename... Ts> struct hash<ArgCapture<Ts...>> {
  size_t operator()(const ArgCapture<Ts...> &c) const {
    size_t result = 0;
    if constexpr (sizeof...(Ts) == 1) {
      return std::hash<Ts...>{}(c.val);
    } else {
      return c.hash_i(result, std::make_index_sequence<sizeof...(Ts)>());
    }
  }
};

template <> struct hash<InstCapture> {
  size_t operator()(const InstCapture &c) const { return 0; }
};

template <> struct hash<BinopCapture> {
  size_t operator()(const BinopCapture &c) const { return 0; }
};

template <> struct hash<PattCapture> {
  size_t operator()(const PattCapture &c) const { return 0; }
};

template <> struct hash<CallCapture> {
  size_t operator()(const CallCapture &c) const { return 0; }
};

template <> struct hash<VarCapture> {
  size_t operator()(const VarCapture &c) const {
    return hash<ArgCapture<int>>{}(c);
  }
};
} // namespace std

namespace {

template <char h, char l, auto display, typename... U>
struct BCDesc : DepTypePoint<from_nibbles(h, l), ArgCapture<U...>> {
  struct PrintProxy {
    const ArgCapture<U...> &params;
    friend std::ostream &operator<<(std::ostream &o, PrintProxy p) {
      return o << display << '\t' << p.params;
    }
  };

  static PrintProxy printable(const ArgCapture<U...> &params) {
    return PrintProxy{params};
  }
};

template <char h, auto display, typename... U>
struct BCDesc2 : BCDesc<h, 0, display, U...> {
  template <typename ArgT> static constexpr bool matches(ArgT other_val) {
    if constexpr (std::is_same_v<ArgT, char>) {
      return DepTypePoint<h, ArgCapture<U...>>::matches(
          to_nibbles(other_val).first);
    }
    return false;
  }
};

// clang-format off
using BytecodeDepType = DependentType<
  DepTypePoint<BC_H::BC_H_BINOP,    BC_L_BINOP::BC_L_BINOP>,
  DepTypePoint<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_STRAIGHT>,
  DepTypePoint<BC_H::BC_H_LD,       BC_L_LDS::BC_L_LDS>,
  DepTypePoint<BC_H::BC_H_LDA,      BC_L_LDS::BC_L_LDS>,
  DepTypePoint<BC_H::BC_H_ST,       BC_L_LDS::BC_L_LDS>,
  DepTypePoint<BC_H::BC_H_CONTROL,  BC_L_CONTROL::BC_L_CONTROL>,
  DepTypePoint<BC_H::BC_H_PATT,     BC_L_PATT::BC_L_PATT>,
  DepTypePoint<BC_H::BC_H_CALL,     BC_L_CALL_RUNTIME::BC_L_CALL_RUNTIME>,
  DepTypePoint<BC_H::BC_H_STOP,     BC_L_STOP::BC_L_STOP>
>;

using BytecodeParamsDepType = DependentType<
  BCDesc2<BC_H::BC_H_BINOP, "BINOP"_d, BinopCapture>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_CONST,  "CONST"_d,  int>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_STRING, "STRING"_d, const char *>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_SEXP,   "SEXP"_d,   const char *, int>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_STI,    "STI"_d>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_STA,    "STA"_d>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_JMP,    "JMP"_d,    void *>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_END,    "END"_d>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_RET,    "RET"_d>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_DROP,   "DROP"_d>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_DUP,    "DUP"_d>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_SWAP,   "SWAP"_d>,
  BCDesc<BC_H::BC_H_STRAIGHT, BC_L_STRAIGHT::BC_L_ELEM,   "ELEM"_d>,
  BCDesc2<BC_H::BC_H_LD,  "LD"_d,  VarCapture>,
  BCDesc2<BC_H::BC_H_LDA, "LDA"_d, VarCapture>,
  BCDesc2<BC_H::BC_H_ST,  "ST"_d,  VarCapture>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_CJMPz,   "CJMPz"_d,   void *>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_CJMPnz,  "CJMPnz"_d,  void *>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_BEGIN,   "BEGIN"_d,   int, int>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_CBEGIN,  "CBEGIN"_d,  int, int>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_CLOSURE, "CLOSURE"_d, void *, int>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_CALLC,   "CALLC"_d,   int>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_CALL,    "CALL"_d,    void *, int>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_TAG,     "TAG"_d,     const char *, int>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_ARRAY,   "ARRAY"_d,   int>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_FAIL,    "FAIL"_d,    int, int>,
  BCDesc<BC_H::BC_H_CONTROL, BC_L_CONTROL::BC_L_LINE,    "LINE"_d,    int>,
  BCDesc2<BC_H::BC_H_PATT, "PATT"_d, PattCapture>,
  BCDesc<BC_H::BC_H_CALL, BC_L_CALL_RUNTIME::BC_L_ARRAY, "CALL"_d, CallCapture, int>,
  BCDesc2<BC_H::BC_H_CALL,                               "CALL"_d, CallCapture>,
  BCDesc<BC_H::BC_H_STOP, BC_L_STOP::BC_L_STP, "STOP"_d>
>;
// clang-format on

/* Analyzer class */
class Analyzer {
  bytefile_ptr bf;

  char *ip;  // Current instruction pointer
  char h, l; // Last high and low nibbles of the instruction bytecode

  template <typename U = char> // defer
  void read_inst() {
    char x = read<U>();
    h = (x & 0xF0) >> 4;
    l = x & 0x0F;
  }

  [[noreturn]] void fail() {
    failure("ERROR: invalid opcode %d-%d\n", h, l);
    abort();
  }

  struct EnumerException : std::out_of_range {
    EnumerException(int val, int min, int max, const std::string &what = "")
        : std::out_of_range("Enum index " + std::to_string(val) +
                            " out of range, expected value [" +
                            std::to_string(min) + "; " + std::to_string(max) +
                            "): " + what) {}

    EnumerException(int val, const std::string &what = "")
        : std::out_of_range("Enum index " + std::to_string(val) +
                            " is not present: " + what) {}
  };

  template <auto enum_min, template <decltype(enum_min)> typename Enumee,
            typename Idxs>
  struct Enumer;

  template <typename EnumT, EnumT enum_min, template <EnumT> typename Enumee,
            int... I>
  struct Enumer<enum_min, Enumee, std::integer_sequence<int, I...>> {
    struct T : std::tuple<Enumee<static_cast<EnumT>(I + enum_min)>...> {
      template <int Ih, int... It, typename FuncT>
      auto visit(EnumT key, FuncT &&func) {
        if (key == static_cast<EnumT>(Ih + enum_min)) {
          if constexpr (Enumee<static_cast<EnumT>(Ih + enum_min)>::is_valid()) {
            return func(std::get<Ih>(*this));
          } else {
            throw EnumerException(key);
          }
        } else if constexpr (sizeof...(It) > 0) {
          return visit<It...>(key, std::forward<FuncT>(func));
        } else {
          throw EnumerException(key, enum_min, enum_min + Ih + 1);
        }
      }

      template <typename FuncT> auto visit(EnumT key, FuncT &&func) {
        return visit<I...>(key, std::forward<FuncT>(func));
      }

      template <int Ih, int... It, typename FuncT> void walk(FuncT &&func) {
        if constexpr (Enumee<static_cast<EnumT>(Ih + enum_min)>::is_valid())
          func(std::get<Ih>(*this));
        if constexpr (sizeof...(It) > 0)
          walk<It...>(func);
      }

      template <typename FuncT> void walk(FuncT &&func) { walk<I...>(func); }
    };
  };

  template <BC_H::BC_H high_val, typename L_T>
  struct LowEnum : LowEnum<high_val, void> {
    using LowT = L_T;

    template <LowT low_val, typename PtT>
    struct ArgsEnum : ArgsEnum<low_val, void> {
      using PointT = PtT;
      using ArgsT = typename PointT::ToT;

      std::unordered_map<ArgsT, size_t> freqs;

      static constexpr bool is_valid() { return true; }
    };

    template <LowT low_val> struct ArgsEnum<low_val, void> {
      static constexpr LowT get_low_val() { return low_val; }
      static constexpr bool is_valid() { return false; }
    };

    static constexpr bool is_valid() { return true; }

    template <LowT low_val>
    using ArgsEnumT =
        ArgsEnum<low_val, typename BytecodeParamsDepType::template ToPointT<
                              from_nibbles(high_val, low_val)>>;

    typename Enumer<
        LowT::BC_L_MIN, ArgsEnumT,
        std::make_integer_sequence<int, LowT::BC_L_MAX - LowT::BC_L_MIN + 1>>::T
        by_low;
  };

  template <BC_H::BC_H high_val> struct LowEnum<high_val, void> {
    static constexpr BC_H::BC_H get_high_val() { return high_val; }
    static constexpr bool is_valid() { return false; }
  };

  template <BC_H::BC_H high_val>
  using LowEnumT = LowEnum<high_val, BytecodeDepType::ToT<high_val>>;

  Enumer<BC_H::BC_H_MIN, LowEnumT,
         std::make_integer_sequence<int, BC_H::BC_H_MAX - BC_H::BC_H_MIN +
                                             1>>::T by_high;

public:
  template <typename T> T read() { return T::read(*this); }

  Analyzer(bytefile_ptr bf) : bf(std::move(bf)) {}

  void analyze() {
    ip = bf->code_ptr;

    while (true) {
      read_inst();
      try {
        by_high.visit(static_cast<BC_H::BC_H>(h), [&](auto &le) {
          using LE_T = std::remove_reference_t<decltype(le)>;
          le.by_low.visit(static_cast<typename LE_T::LowT>(l), [&](auto &ae) {
            using AE_T = std::remove_reference_t<decltype(ae)>;
            using ArgsT = typename AE_T::ArgsT;
            ArgsT args = ArgsT::read(*this);
            ae.freqs[args]++;
          });
        });
      } catch (EnumerException e) {
        fail();
      }
      if (h == BC_H::BC_H_STOP)
        break;
    }

    std::multimap<size_t, std::string, std::greater<size_t>> sorted;

    by_high.walk([&](auto &le) {
      using LE_T = std::remove_reference_t<decltype(le)>;
      le.by_low.walk([&](auto &ae) {
        using AE_T = std::remove_reference_t<decltype(ae)>;
        using PointT = typename AE_T::PointT;
        for (auto &[args, val] : ae.freqs) {
          std::stringstream ss;
          ss << PointT::printable(args);
          sorted.emplace(val, ss.str());
        }
      });
    });

    for (auto &[freq, inst] : sorted)
      Logger::log(freq, '\t', inst, '\n');
  }
};

template <> int Analyzer::read<int>() {
  ip += sizeof(int);
  return *(int *)(ip - sizeof(int));
}

template <> char Analyzer::read<char>() { return *ip++; }

template <> void *Analyzer::read<void *>() { return (void *)read<int>(); }

template <> const char *Analyzer::read<const char *>() {
  return bf->get_string(read<int>());
}

template <> InstCapture Analyzer::read<InstCapture>() { return {h, l}; }

/* Dumps the contents of the file */
void dump_file(bytefile_ptr bf) {
  Analyzer analyzer(std::move(bf));
  analyzer.analyze();
}

} // anonymous namespace

int main(int argc, char *argv[]) {
  dump_file(read_file(argv[1]));
  return 0;
}

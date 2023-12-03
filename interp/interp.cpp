/* Lama SM Bytecode interpreter */

#include <algorithm>
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <memory>
#include <stack>
#include <string>

extern "C" {
#include "../runtime/runtime_common.h"
#include "../runtime/runtime.h"
#include "../runtime/gc.h"

  extern size_t __gc_stack_top, __gc_stack_bottom;

  int Lwrite(int n);
  int Lread();
  int Llength(void *p);
  int LtagHash(char *s);
  void *Lstring(void *p);

  void *Bstring(void *p);
  void *Belem(void *p, int i);
  void *Bsta(void *v, int i, void *x);
  void *Barray(int bn, ...);
  void *Bsexp(int n, ...);
  int Btag(void *d, int t, int n);
  void *Bclosure(int bn, void *entry, ...);
  int Barray_patt(void *d, int n);
  int Bstring_patt(void *x, void *y);
  int Bclosure_tag_patt(void *x);
  int Bboxed_patt(void *x);
  int Bunboxed_patt(void *x);
  int Barray_tag_patt(void *x);
  int Bstring_tag_patt(void *x);
  int Bsexp_tag_patt(void *x);
  void Bmatch_failure(void *v, char *fname, int line, int col);
}

namespace {
class Logger {
private:
  Logger(std::ostream &o) : o(&o) {}
  Logger() = default;

  std::ostream *o = nullptr;

  static Logger instance;

  template<typename... ArgTs>
  Logger &log_(ArgTs &&... args) {
    if (o) {
      using expander = int[];
      (void)expander{0, (void(*o << std::forward<ArgTs>(args)), 0)...};
    }
    return *this;
  }

public:

  template<typename... ArgTs>
  static Logger &log(ArgTs &&... args) {
    return instance.log_(std::forward<ArgTs>(args)...);
  }
};

#ifdef DEBUG
Logger Logger::instance(std::cerr);
#define INTERP_DEBUG(x)                                                        \
  do {                                                                         \
    x;                                                                         \
  } while (false);
#else
Logger Logger::instance{};
#define INTERP_DEBUG(x)
#endif

// Call function on another stack assembly language helper
extern "C" size_t call_function_with_stack(void *st, void *f);

// Because &__{start,end}_custom_data are used in GC as a range of addresses of
// the custom data (addresses, not values), I can only statically allocate some
// global area (or use stack for it)
constexpr size_t MAX_GLOBAL_AREA_SIZE = 32;
size_t global_area[MAX_GLOBAL_AREA_SIZE]
    __attribute__((section("custom_data"))){};

/* The unpacked representation of bytecode file */
struct bytefile {
  char *string_ptr;                     /* A pointer to the beginning of the string table */
  int  *public_ptr;                     /* A pointer to the beginning of publics table    */
  char *code_ptr;                       /* A pointer to the bytecode itself               */
  int   stringtab_size;                 /* The size (in bytes) of the string table        */
  int   global_area_size;               /* The size (in words) of global area             */
  int   public_symbols_number;          /* The number of public symbols                   */
  char  buffer[0];

  bytefile(FILE *f, long size) {
    if (fread(&stringtab_size, sizeof(stringtab_size), 1, f) != 1 ||
        fread(&global_area_size, sizeof(stringtab_size), 1, f) != 1 ||
        fread(&public_symbols_number, sizeof(stringtab_size), 1, f) != 1)
      failure("%s\n", strerror(errno));

    if (global_area_size > MAX_GLOBAL_AREA_SIZE)
      failure("%d is too many global variables (maximum is %d)",
              global_area_size, MAX_GLOBAL_AREA_SIZE);

    size -= sizeof(int) * 3;

    if (size != fread(buffer, 1, size, f))
      failure("%s\n", strerror(errno));

    string_ptr  = &buffer[public_symbols_number * 2 * sizeof(int)];
    public_ptr  = (int *)buffer;
    code_ptr    = &string_ptr[stringtab_size];
  }

  /* Gets a string from a string table by an index */
  const char *get_string(int pos) const {
    return &string_ptr[pos];
  }

  /* Gets a name for a public symbol */
  const char *get_public_name(int i) const {
    return get_string(public_ptr[i * 2]);
  }

  /* Gets an offset for a public symbol */
  int get_public_offset(int i) const {
    return public_ptr[i * 2 + 1];
  }

  /* Gets a pointer to the global variable */
  size_t *get_global(int i) {
    return &global_area[i];
  }

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
  BC_H_BINOP = 0,
  BC_H_STRAIGHT,
  BC_H_LD,
  BC_H_LDA,
  BC_H_ST,
  BC_H_CONTROL,
  BC_H_PATT,
  BC_H_CALL,
  BC_H_STOP = 15
};
}

namespace BC_L_BINOP {
enum BC_L_BINOP {
  BC_L_ADD = 1,
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
  BC_L_OR
};
}

namespace BC_L_STRAIGHT {
enum BC_L_STRAIGHT {
  BC_L_CONST,
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
  BC_L_ELEM
};
}

namespace BC_L_LDS {
enum BC_L_LDS { BC_L_G, BC_L_L, BC_L_A, BC_L_C };
}

namespace BC_L_CONTROL {
enum BC_L_CONTROL {
  BC_L_CJMPz,
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
};
}

namespace BC_L_CALL_RUNTIME {
enum BC_L_CALL_RUNTIME { BC_L_READ, BC_L_WRITE, BC_L_LENGTH, BC_L_STRING, BC_L_ARRAY };
}

namespace BC_L_PATT {
enum BC_L_PATT {
  BC_L_EQ_STR,
  BC_L_STRING,
  BC_L_ARRAY,
  BC_L_SEXP,
  BC_L_BOX,
  BC_L_VAL,
  BC_L_FUN
};
}

constexpr size_t RUNTIME_VSTACK_SIZE = 100000;

/* Virtual stack wrapper */
class VirtStack {
  size_t buf[RUNTIME_VSTACK_SIZE + 1];
  size_t cur = RUNTIME_VSTACK_SIZE;

public:
  VirtStack() { buf[cur] = 0; }

  void push(size_t value) {
    assert(cur != 0);
    buf[--cur] = value;
  }

  size_t pop() {
    assert(cur != RUNTIME_VSTACK_SIZE);
    return buf[cur++];
  }

  void multipop(size_t n) {
    cur += n;
    assert(cur <= RUNTIME_VSTACK_SIZE);
  }

  size_t peek() { return buf[cur]; }

  void *top() { return &buf[cur]; }
  void *bottom() { return &buf[RUNTIME_VSTACK_SIZE]; }

  size_t size() { return RUNTIME_VSTACK_SIZE - cur; }

  size_t *kth_from_bottom(size_t k) {
    assert(size() >= k);
    return &buf[RUNTIME_VSTACK_SIZE - 1 - k];
  }

  size_t *kth_from_top(size_t k) {
    assert(size() >= k);
    return &buf[cur + k];
  }

  /* Call function on this stack */
  template <typename RetT, typename... ArgTs>
  size_t call_runtime_function(RetT (*f)(ArgTs...)) {
    return call_function_with_stack((char *)top(), (void *)f);
  }

  template <typename RetT, typename... ArgTs>
  size_t call_runtime_function(RetT (*f)(ArgTs..., ...)) {
    return call_function_with_stack((char *)top(), (void *)f);
  }

  static void print_object_info(void *obj_content) {
    data  *d       = TO_DATA(obj_content);
    size_t obj_tag = TAG(d->data_header);
    size_t obj_id =
#ifdef DEBUG_VERSION
        d->id;
#else
        0;
#endif
    Logger::log("id ", obj_id, " tag ", obj_tag, " | ");
  }

  static void print_unboxed(int unboxed) {
    Logger::log("unboxed ", UNBOX(unboxed), " | ");
  }

  static void print_info(size_t value) {
    if (is_valid_heap_pointer((size_t *)value)) {
      Logger::log((void *)value, ", ");
      print_object_info((void *)value);
    } else {
      print_unboxed((int)value);
    }
  }

  void print_stack_content() {
    Logger::log("\nStack content:\n");
    for (size_t *stack_ptr = kth_from_top(0); stack_ptr <= kth_from_bottom(0);
         ++stack_ptr) {
      size_t value = *stack_ptr;
      print_info(value);
      Logger::log("\n");
    }
    Logger::log("Stack content end.");
  }
};

/* GC wrapper */
class GC {
public:
  GC() { __init(); }

  void set_stack(void *top, void *bottom) {
    __gc_stack_top = (size_t)top - 4;
    __gc_stack_bottom = (size_t)bottom;
  }

  void set_stack(VirtStack &st) {
    set_stack(st.top(), st.bottom());
  }
};

/* Interpreter class */
class Interpreter {
  bytefile_ptr bf;
  GC gc;
  std::unique_ptr<VirtStack> st = std::make_unique<VirtStack>();

  char *get_entry_point() {
    using namespace std::string_literals;
    for (int i = 0; i < bf->public_symbols_number; i++)
      if ("main"s == bf->get_public_name(i))
        return bf->code_ptr + bf->get_public_offset(i);

    return nullptr;
  }

  const char *ops[13] = {
      "+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
  const char *pats[7] = {"=str", "#string", "#array", "#sexp",
                         "#box", "#val",    "#fun"};
  const char *lds[3] = {"LD", "LDA", "ST"};

  char *ip;  // Current instruction pointer
  char h, l; // Last high and low nibbles of the instruction bytecode

  int read_int() {
    ip += sizeof(int);
    return *(int *)(ip - sizeof(int));
  }

  const char read_byte() { return *ip++; }

  const char *read_string() { return bf->get_string(read_int()); }

  void read_inst() {
    char x = read_byte();
    h = (x & 0xF0) >> 4;
    l = x & 0x0F;
  }

  [[noreturn]] void fail() {
    failure("ERROR: invalid opcode %d-%d\n", h, l);
    abort();
  }

  /* Pass through functions to the stack */
  size_t pop() {
    size_t res = st->pop();
    gc.set_stack(*st);
    return res;
  }

  int pop_unbox() {
    size_t res = pop();
    if (!UNBOXED(res))
      failure("Expected value entry on stack!");
    return UNBOX(res);
  }

  size_t erase(size_t k_from_top) {
    swap_args(k_from_top + 1);
    size_t res = pop();
    swap_args(k_from_top);
    gc.set_stack(*st);
    return res;
  }

  void multipop(size_t n) {
    st->multipop(n);
    gc.set_stack(*st);
  }

  size_t peek() {
    return st->peek();
  }

  void *top() {
    return st->top();
  }

  void push(size_t value) {
    st->push(value);
    gc.set_stack(*st);
  }

  size_t stack_size() {
    return st->size();
  }

  // Reverse the order of last n stack entries
  void swap_args(size_t n) {
    std::reverse(st->kth_from_top(0), st->kth_from_top(n));
  }

  /* Runtime functions need to be called on the virtual stack - calls and clears
   * the arguments off the stack */
  template <typename RetT, typename... ArgTs>
  size_t call_runtime_function(RetT (*f)(ArgTs...)) {
    size_t nargs = sizeof...(ArgTs);
    size_t res = st->call_runtime_function(f);
    st->multipop(nargs);
    return res;
  }

  template <typename RetT, typename... ArgTs>
  size_t call_runtime_function(RetT (*f)(ArgTs..., ...), size_t nvars) {
    size_t nargs = sizeof...(ArgTs) + nvars;
    size_t res = st->call_runtime_function(f);
    st->multipop(nargs);
    return res;
  }

  /* Call stack entry */
  struct stack_frame {
    char *return_address; // The return address, inside the code buffer
    size_t vstack_begin;  // Stack index from where closure, args and locals start
    bool is_closure;      // Flag if closure is present for this function
    int n_args;           // Number of arguments
    int n_locals;         // Number of local variables

    stack_frame(char *return_address, size_t vstack_begin, bool is_closure,
                int n_args, int n_locals)
        : return_address(return_address),
          vstack_begin(
              vstack_begin - n_args -
              is_closure), // arguments and closure are already on stack
          is_closure(is_closure), n_args(n_args), n_locals(n_locals) {}

    size_t closure() const { return vstack_begin; }

    size_t arg(size_t k) const {
      return vstack_begin + is_closure + k;
    }

    size_t local(size_t k) const {
      return vstack_begin + is_closure + n_args + k;
    }

    void print_frame() const {
      Logger::log("\nret addr ", (void *)return_address, "\nclosure [",
                  vstack_begin, "; ", vstack_begin + is_closure, ")\nargs [",
                  vstack_begin + is_closure, "; ",
                  vstack_begin + is_closure + n_args, ")\nlocals [",
                  vstack_begin + is_closure + n_args, "; ",
                  vstack_begin + is_closure + n_args + n_locals, ")");
    }
  };

  /* Pass through functions to the last call stack entry */
  size_t *arg(size_t k) {
    return st->kth_from_bottom(call_stack.top().arg(k));
  }

  size_t *captured(size_t k) {
    size_t closure = *st->kth_from_bottom(call_stack.top().closure());
    data *a = TO_DATA((void *)closure);
    return &((size_t *)a->contents)[k + 1];
  }

  size_t *local(size_t k) {
    return st->kth_from_bottom(call_stack.top().local(k));
  }

  std::stack<stack_frame> call_stack;

  void alloc_locals(size_t n) {
    for (size_t i = 0; i < n; i++)
      push(0);
  }

  size_t *get_var(char l, int idx) {
    using namespace BC_L_LDS;
    switch (l) {
    case BC_L_G:
      Logger::log("G(", idx, ")");
      return bf->get_global(idx);
      break;
    case BC_L_L:
      Logger::log("L(", idx, ")");
      return local(idx);
      break;
    case BC_L_A:
      Logger::log("A(", idx, ")");
      return arg(idx);
      break;
    case BC_L_C:
      Logger::log("C(", idx, ")");
      return captured(idx);
    default:
      fail();
    }
  }

public:
  Interpreter(bytefile_ptr bf) : bf(std::move(bf)) {}

  void interpret() {
    // call main with 2 args
    push(0);
    push(0);
    call_stack.emplace(nullptr, stack_size(), false, 2, 0);
    ip = get_entry_point();

    while (ip != nullptr) {
      read_inst();
      Logger::log("0x", std::hex, std::setw(8), std::setfill('0'),
                  ip - bf->code_ptr - 1, ":\t");

      using namespace BC_H;
      switch (h) {
      case BC_H_STOP:
        ip = nullptr;
        break;

      case BC_H_BINOP: {
        Logger::log("BINOP\t", ops[l - 1]);
        int Y = UNBOX(pop());
        int X = UNBOX(pop());
        int R{};
        using namespace BC_L_BINOP;
        switch (l) {
        case BC_L_ADD:
          R = X + Y;
          break;
        case BC_L_SUB:
          R = X - Y;
          break;
        case BC_L_MUL:
          R = X * Y;
          break;
        case BC_L_DIV:
          R = X / Y;
          break;
        case BC_L_MOD:
          R = X % Y;
          break;
        case BC_L_LT:
          R = X < Y;
          break;
        case BC_L_LTE:
          R = X <= Y;
          break;
        case BC_L_GT:
          R = X > Y;
          break;
        case BC_L_GTE:
          R = X >= Y;
          break;
        case BC_L_EQ:
          R = X == Y;
          break;
        case BC_L_NEQ:
          R = X != Y;
          break;
        case BC_L_AND:
          R = X && Y;
          break;
        case BC_L_OR:
          R = X || Y;
          break;
        default:
          fail();
        }
        push(BOX(R));
        break;
      }

      case BC_H_STRAIGHT: {
        using namespace BC_L_STRAIGHT;
        switch (l) {
        case BC_L_CONST: {
          size_t R = read_int();
          Logger::log("CONST\t", R);
          push(BOX(R));
          break;
        }
        case BC_L_STRING: {
          const char *string = read_string();
          Logger::log("STRING\t", string);
          push((size_t)string);
          push(call_runtime_function(Bstring));
          break;
        }
        case BC_L_SEXP: {
          const char *tag = read_string();
          int n = read_int();
          Logger::log("SEXP\t ", tag, " ", n);
          push((size_t)tag);
          push(call_runtime_function(LtagHash));
          swap_args(n + 1);
          push(BOX(n + 1));
          push(call_runtime_function(Bsexp, n + 1));
          break;
        }
        case BC_L_STI: // Unsure if it's generated => not tested
          Logger::log("STI");
          push(0);
          swap_args(2);
          push(call_runtime_function(Bsta));
          break;

        case BC_L_STA:
          Logger::log("STA");
          if (!UNBOXED(*st->kth_from_top(1))) {
            push(0);
            swap_args(2);
          }
          push(call_runtime_function(Bsta));
          break;

        case BC_L_JMP: {
          int to = read_int();
          Logger::log("JMP\t0x", std::hex, std::setw(8), std::setfill('0'), to);
          ip = &bf->code_ptr[to];
          break;
        }
        case BC_L_END:
        case BC_L_RET: { // Unsure if it's generated => not tested
          Logger::log(l == BC_L_END ? "END" : "RET");
          size_t ret = pop();
          {
            auto &frame = call_stack.top();
            Logger::log("\n -> popped ", stack_size() - frame.vstack_begin,
                        " elems");
            multipop(stack_size() - frame.vstack_begin);
            ip = frame.return_address;
          }
          call_stack.pop();
          push(ret);
          INTERP_DEBUG(st->print_stack_content());
          break;
        }
        case BC_L_DROP:
          Logger::log("DROP");
          pop();
          break;

        case BC_L_DUP:
          Logger::log("DUP");
          push(peek());
          break;

        case BC_L_SWAP: // Unsure if it's generated => not tested
          Logger::log("SWAP");
          swap_args(2);
          break;

        case BC_L_ELEM: {
          Logger::log("ELEM");
          swap_args(2);
          push(call_runtime_function(Belem));
          break;
        }
        default:
          fail();
        }
        break;
      }
      case BC_H_LD:
      case BC_H_ST:
      case BC_H_LDA: {
        Logger::log(lds[h - 2], "\t");
        int idx = read_int();
        size_t *ptr = get_var(l, idx);
        switch (h) {
        case BC_H_LD:
          push(*ptr);
          break;
        case BC_H_LDA:
          push((size_t)ptr);
          break;
        case BC_H_ST:
          *ptr = peek();
          break;
        default:
          fail();
        }
        break;
      }
      case BC_H_CONTROL: {
        using namespace BC_L_CONTROL;
        switch (l) {
        case BC_L_CJMPz: {
          int to = read_int();
          Logger::log("CJMPz\t0x", std::hex, std::setw(8), std::setfill('0'), to);
          if (UNBOX(pop()) == 0)
            ip = &bf->code_ptr[to];
          break;
        }
        case BC_L_CJMPnz: {
          int to = read_int();
          Logger::log("CJMPnz\t0x", std::hex, std::setw(8), std::setfill('0'), to);
          if (UNBOX(pop()))
            ip = &bf->code_ptr[to];
          break;
        }
        case BC_L_BEGIN:
        case BC_L_CBEGIN: {
          int n_args = read_int();
          int n_locals = read_int();
          Logger::log(l == BC_L_BEGIN ? "" : "C", "BEGIN\t", n_args, " ",
                      n_locals);
          auto &frame = call_stack.top();
          if (n_args != frame.n_args)
            failure("Function call with the wrong number of arguments %d "
                    "(expected %d)!",
                    frame.n_args, n_args);
          if (l == BC_L_CBEGIN && !frame.is_closure)
            failure("Calling closure function without closure!");
          frame.n_locals = n_locals;
          frame.print_frame();
          alloc_locals(n_locals);
          break;
        }
        case BC_L_CLOSURE: {
          int addr = read_int();
          Logger::log("CLOSURE\t0x", std::hex, std::setw(8), std::setfill('0'),
                      addr);
          int n = read_int();
          for (int i = 0; i < n; i++) {
            char l = read_byte();
            int idx = read_int();
            Logger::log("\n-> ", i, "-th capture: ");
            size_t *ptr = get_var(l, idx);
            VirtStack::print_info(*ptr);
            push(*ptr);
          }
          swap_args(n);
          push(addr);
          push(BOX(n));
          push(call_runtime_function(Bclosure, n));
          break;
        }
        case BC_L_CALLC: {
          int n_args = read_int();
          Logger::log("CALLC\t", n_args);
          INTERP_DEBUG(Logger::log("\n-> stack state before:");
                       st->print_stack_content());
          data *closure = TO_DATA((void *)*st->kth_from_top(n_args));
          if (TAG(closure->data_header) != CLOSURE_TAG)
            failure("Expected closure entry on stack, got %d!",
                    TAG(closure->data_header));
          int addr = (int)((size_t *)closure->contents)[0];
          call_stack.emplace(ip, stack_size(), true, n_args, 0);
          ip = &bf->code_ptr[addr];
          INTERP_DEBUG(Logger::log("\n-> stack state after:");
                       st->print_stack_content());
          break;
        }
        case BC_L_CALL: {
          int addr = read_int();
          int n_args = read_int();
          Logger::log("CALL\t0x", std::hex, std::setw(8), std::setfill('0'), addr,
                      " ", n_args);
          call_stack.emplace(ip, stack_size(), false, n_args, 0);
          ip = &bf->code_ptr[addr];
          INTERP_DEBUG(st->print_stack_content());
          break;
        }
        case BC_L_TAG: {
          const char *tag = read_string();
          int n = read_int();
          Logger::log("TAG\t ", tag, " ", n);
          push((size_t)tag);
          push(call_runtime_function(LtagHash));
          push(BOX(n));
          swap_args(3);
          push(call_runtime_function(Btag));
          break;
        }
        case BC_L_ARRAY: {
          int n = read_int();
          Logger::log("ARRAY\t", n);
          push(BOX(n));
          swap_args(2);
          push(call_runtime_function(Barray_patt));
          break;
        }
        case BC_L_FAIL: {
          int line = read_int(), col = read_int();
          Logger::log("FAIL\t", line, ":", col);
          push((size_t)"<unknown>");
          push(BOX(line));
          push(BOX(col));
          swap_args(4);
          call_runtime_function(Bmatch_failure); // noreturn
          abort();
          break;
        }
        case BC_L_LINE:
          Logger::log("LINE\t", read_int());
          break;

        default:
          fail();
        }
        break;
      }
      case BC_H_PATT: {
        Logger::log("PATT\t", pats[l]);
        using namespace BC_L_PATT;
        switch (l) {
        case BC_L_EQ_STR:
          push(call_runtime_function(Bstring_patt));
          break;
        case BC_L_STRING:
          push(call_runtime_function(Bstring_tag_patt));
          break;
        case BC_L_ARRAY:
          push(call_runtime_function(Barray_tag_patt));
          break;
        case BC_L_SEXP:
          push(call_runtime_function(Bsexp_tag_patt));
          break;
        case BC_L_BOX:
          push(call_runtime_function(Bboxed_patt));
          break;
        case BC_L_VAL:
          push(call_runtime_function(Bunboxed_patt));
          break;
        case BC_L_FUN:
          push(call_runtime_function(Bclosure_tag_patt));
          break;
        default:
          fail();
        }
        break;
      }
      case BC_H_CALL: {
        using namespace BC_L_CALL_RUNTIME;
        switch (l) {
        case BC_L_READ:
          Logger::log("CALL\tLread");
          push(call_runtime_function(Lread));
          break;

        case BC_L_WRITE: {
          Logger::log("CALL\tLwrite");
          push(call_runtime_function(Lwrite));
          break;
        }
        case BC_L_LENGTH:
          Logger::log("CALL\tLlength");
          push(call_runtime_function(Llength));
          break;

        case BC_L_STRING:
          Logger::log("CALL\tLstring");
          push(call_runtime_function(Lstring));
          break;

        case BC_L_ARRAY: {
          int n = read_int();
          Logger::log("CALL\tBarray\t", n);
          swap_args(n);
          push(BOX(n));
          push(call_runtime_function(Barray, n));
          break;
        }
        default:
          fail();
        }
      } break;

      default:
        fail();
      }

      Logger::log("\n");
    }
    Logger::log("\n<end>\n");
  }
};

/* Dumps the contents of the file */
void dump_file (bytefile_ptr bf) {
  int i;
  
  Logger::log("String table size       : ", bf->stringtab_size, "\n");
  Logger::log("Global area size        : ", bf->global_area_size, "\n");
  Logger::log("Number of public symbols: ", bf->public_symbols_number, "\n");
  Logger::log("Public symbols          :\n");

  for (i = 0; i < bf->public_symbols_number; i++)
    Logger::log("   0x", std::hex, std::setw(8), std::setfill('0'),
                bf->get_public_offset(i), ": ", bf->get_public_name(i), "\n");

  Logger::log("Code:\n");
  Interpreter interp(std::move(bf));
  interp.interpret();
}

} // anonymous namespace

int main (int argc, char* argv[]) {
  dump_file(read_file(argv[1]));
  return 0;
}

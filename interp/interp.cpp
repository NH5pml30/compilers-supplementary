/* Lama SM Bytecode interpreter */

#include <cstring>
#include <cstdio>
#include <cerrno>
#include <cstdlib>
#include <string>
#include <memory>
#include <stack>
#include <algorithm>

extern "C" {
#include "../runtime/runtime_common.h"
#include "../runtime/runtime.h"
#include "../runtime/virt_stack.h"
#include "../runtime/gc.h"

  void *__start_custom_data;
  void *__stop_custom_data;
  extern size_t __gc_stack_top, __gc_stack_bottom;

  int Lwrite (int n);
  int Lread ();
  int Llength (void *p);

  void *Bstring (void *p);
  void *Belem (void *p, int i);
  void *Bsta (void *v, int i, void *x);
  void *Barray (int bn, ...);
}

extern "C" size_t call_function_with_stack(void *st, void *f);

/* The unpacked representation of bytecode file */
struct bytefile {
  char *string_ptr;                     /* A pointer to the beginning of the string table */
  int  *public_ptr;                     /* A pointer to the beginning of publics table    */
  char *code_ptr;                       /* A pointer to the bytecode itself               */
  std::unique_ptr<size_t[]> global_ptr; /* A pointer to the global area                   */
  int   stringtab_size;                 /* The size (in bytes) of the string table        */
  int   global_area_size;               /* The size (in words) of global area             */
  int   public_symbols_number;          /* The number of public symbols                   */
  char  buffer[0];

  bytefile(FILE *f, long size) {
    if (fread(&stringtab_size, sizeof(stringtab_size), 1, f) != 1 ||
        fread(&global_area_size, sizeof(stringtab_size), 1, f) != 1 ||
        fread(&public_symbols_number, sizeof(stringtab_size), 1, f) != 1)
      failure("%s\n", strerror(errno));

    size -= sizeof(int) * 3;

    if (size != fread(buffer, 1, size, f))
      failure("%s\n", strerror(errno));

    string_ptr  = &buffer[public_symbols_number * 2 * sizeof(int)];
    public_ptr  = (int *)buffer;
    code_ptr    = &string_ptr[stringtab_size];
    global_ptr  = std::make_unique<size_t[]>(global_area_size);
    __start_custom_data = (char *)global_ptr.get();
    __stop_custom_data = (char *)global_ptr.get() + global_area_size;
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

  size_t *get_global(int i) {
    return &global_ptr[i];
  }

  static void deleter(bytefile *p) {
    std::destroy_at(p);
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
  bytefile *file = (bytefile *)operator new(sizeof(intptr_t) * 4 + size);
  rewind(f);
  new (file) bytefile(f, size);
  fclose(f);

  return bytefile_ptr(file, bytefile::deleter);
}

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
  BC_L_ADD = 0,
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

class VirtStack {
  virt_stack *st;

public:
  VirtStack() : st(vstack_create()) { vstack_init(st); }

  void push(size_t value) { vstack_push(st, value); }

  size_t pop() { return vstack_pop(st); }

  void multipop(size_t n) {
    st->cur += n;
    if (st->cur > RUNTIME_VSTACK_SIZE) { assert(0); }
  }

  size_t peek() {
    size_t val = vstack_pop(st);
    vstack_push(st, val);
    return val;
  }

  void *top() { return vstack_top(st); }

  void *bottom() { return (size_t *)vstack_top(st) + vstack_size(st); }

  size_t size() {
    return vstack_size(st);
  }

  size_t *kth_from_start(size_t k) {
    assert(vstack_size(st) > k);
    return &st->buf[RUNTIME_VSTACK_SIZE - 1 - k];
  }

  template <typename RetT, typename... ArgTs>
  size_t call_runtime_function(RetT (*f)(ArgTs...)) {
    size_t res = call_function_with_stack((char *)top(), (void *)f);
    multipop(sizeof...(ArgTs));
    return res;
  }

  template <typename RetT, typename... ArgTs>
  size_t call_runtime_function(RetT (*f)(ArgTs..., ...), size_t nvars) {
    size_t res = call_function_with_stack((char *)top(), (void *)f);
    multipop(sizeof...(ArgTs) + nvars);
    return res;
  }

  ~VirtStack() { vstack_destruct(st); }
};

class GC {
public:
  GC() { __init(); }

  void set_stack(VirtStack &st) {
    __gc_stack_top = (size_t)st.top() - 4;
    __gc_stack_bottom = (size_t)st.bottom();
  }
};

class Interpreter {
  bytefile_ptr bf;
  GC gc;
  VirtStack st;

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
                         "#ref", "#val",    "#fun"};
  const char *lds[3] = {"LD", "LDA", "ST"};

  char *ip, *last_ip{};
  char h, l;

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

  size_t pop() {
    size_t res = st.pop();
    gc.set_stack(st);
    return res;
  }

  size_t peek() {
    return st.peek();
  }

  void *top() {
    return st.top();
  }

  void push(size_t value) {
    st.push(value);
    gc.set_stack(st);
  }

  size_t stack_size() {
    return st.size();
  }

  void swap_args(size_t n) {
    std::reverse((size_t *)st.top(), (size_t *)st.top() + n);
  }

  template <typename RetT, typename... ArgTs>
  size_t call_runtime_function(RetT (*f)(ArgTs...)) {
    return st.call_runtime_function(f);
  }

  template <typename RetT, typename... ArgTs>
  size_t call_runtime_function(RetT (*f)(ArgTs..., ...), size_t nvars) {
    return st.call_runtime_function(f, nvars);
  }

  size_t *local(size_t k) {
    return st.kth_from_start(call_stack.top().vstack_begin +
                             call_stack.top().n_args + k);
  }

  size_t *arg(size_t k) {
    return st.kth_from_start(call_stack.top().vstack_begin + k);
  }

  struct stack_frame {
    char *return_address;
    size_t vstack_begin;
    size_t n_args;
    size_t n_locals;
  };

  std::stack<stack_frame> call_stack;

  void alloc_locals(size_t n) {
    for (size_t i = 0; i < n; i++)
      push(0);
  }

  void dealloc_locals(size_t n) {
    for (size_t i = 0; i < n; i++)
      pop();
  }

public:
  Interpreter(bytefile_ptr bf) : bf(std::move(bf)) {}

  void interpret(FILE *f) {
    ip = get_entry_point();

    while (ip != nullptr) {
      read_inst();
      fprintf(f, "0x%.8x:\t", ip - bf->code_ptr - 1);

      using namespace BC_H;
      switch (h) {
      case BC_H_STOP:
        goto stop;

      /* BINOP */
      case BC_H_BINOP: {
        fprintf(f, "BINOP\t%s", ops[l - 1]);
        int Y = UNBOX(pop());
        int X = UNBOX(pop());
        int R{};
        using namespace BC_L_BINOP;
        switch (l - 1) {
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
        }
        push(BOX(R));
        break;
      }

      case BC_H_STRAIGHT: {
        using namespace BC_L_STRAIGHT;
        switch (l) {
        case BC_L_CONST: {
          size_t R = read_int();
          fprintf(f, "CONST\t%d", R);
          push(BOX(R));
          break;
        }

        case BC_L_STRING: {
          const char *string = read_string();
          fprintf(f, "STRING\t%s", string);
          push((size_t)string);
          push(call_runtime_function(Bstring));
          break;
        }
        case 2:
          fprintf(f, "SEXP\t%s ", read_string());
          fprintf(f, "%d", read_int());
          break;

        case 3:
          fprintf(f, "STI");
          break;

        case 4: {
          fprintf(f, "STA");
          push(call_runtime_function(Bsta));
          break;
        }
        case BC_L_JMP: {
          int to = read_int();
          fprintf(f, "JMP\t0x%.8x", to);
          ip = &bf->code_ptr[to];
          break;
        }
        case BC_L_END: {
          fprintf(f, "END");
          size_t ret = pop();
          dealloc_locals(stack_size() - call_stack.top().vstack_begin -
                         call_stack.top().n_args);
          ip = call_stack.top().return_address;
          call_stack.pop();
          push(ret);
          break;
        }
        case 7:
          fprintf(f, "RET");
          break;

        case BC_L_DROP:
          fprintf(f, "DROP");
          pop();
          break;

        case 9:
          fprintf(f, "DUP");
          break;

        case 10:
          fprintf(f, "SWAP");
          break;

        case BC_L_ELEM: {
          fprintf(f, "ELEM");
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
      case BC_H_ST: {
        fprintf(f, "%s\t", lds[h - 2]);
        int idx = read_int();
        size_t *ptr{};
        using namespace BC_L_LDS;
        switch (l) {
        case BC_L_G:
          fprintf(f, "G(%d)", idx);
          ptr = bf->get_global(idx);
          break;
        case 1:
          fprintf(f, "L(%d)", idx);
          ptr = local(idx);
          break;
        case 2:
          fprintf(f, "A(%d)", idx);
          ptr = arg(idx);
          break;
        case 3:
          fprintf(f, "C(%d)", idx);
          break;
        default:
          fail();
        }
        switch (h) {
        case BC_H_LD:
          push(*ptr);
          break;
        case BC_H_ST:
          *ptr = peek();
          break;
        }
        break;
      }
      case 3:
        fprintf(f, "%s\t", lds[h - 2]);
        switch (l) {
        case 0:
          fprintf(f, "G(%d)", read_int());
          break;
        case 1:
          fprintf(f, "L(%d)", read_int());
          break;
        case 2:
          fprintf(f, "A(%d)", read_int());
          break;
        case 3:
          fprintf(f, "C(%d)", read_int());
          break;
        default:
          fail();
        }
        break;
      case BC_H_CONTROL: {
        using namespace BC_L_CONTROL;
        switch (l) {
        case BC_L_CJMPz: {
          int to = read_int();
          fprintf(f, "CJMPz\t0x%.8x", to);
          if (UNBOX(pop()) == 0)
            ip = &bf->code_ptr[to];
          break;
        }
        case BC_L_CJMPnz: {
          int to = read_int();
          fprintf(f, "CJMPnz\t0x%.8x", to);
          if (UNBOX(pop()))
            ip = &bf->code_ptr[to];
          break;
        }
        case BC_L_BEGIN: {
          int n_args = read_int();
          int n_locals = read_int();
          fprintf(f, "BEGIN\t%d %d", n_args, n_locals);
          call_stack.push({last_ip, stack_size() - n_args, (size_t)n_args,
                           (size_t)n_locals});
          alloc_locals(n_locals);
          break;
        }
        case 3:
          fprintf(f, "CBEGIN\t%d ", read_int());
          fprintf(f, "%d", read_int());
          break;

        case 4:
          fprintf(f, "CLOSURE\t0x%.8x", read_int());
          {
            int n = read_int();
            for (int i = 0; i < n; i++) {
              switch (read_byte()) {
              case 0:
                fprintf(f, "G(%d)", read_int());
                break;
              case 1:
                fprintf(f, "L(%d)", read_int());
                break;
              case 2:
                fprintf(f, "A(%d)", read_int());
                break;
              case 3:
                fprintf(f, "C(%d)", read_int());
                break;
              default:
                fail();
              }
            }
          };
          break;

        case 5:
          fprintf(f, "CALLC\t%d", read_int());
          break;

        case BC_L_CALL: {
          int addr = read_int();
          int n_args = read_int();
          fprintf(f, "CALL\t0x%.8x %d", addr, n_args);
          last_ip = ip;
          ip = &bf->code_ptr[addr];
          break;
        }
        case 7:
          fprintf(f, "TAG\t%s ", read_string());
          fprintf(f, "%d", read_int());
          break;

        case 8:
          fprintf(f, "ARRAY\t%d", read_int());
          break;

        case 9:
          fprintf(f, "FAIL\t%d", read_int());
          fprintf(f, "%d", read_int());
          break;

        case BC_L_LINE:
          fprintf(f, "LINE\t%d", read_int());
          break;

        default:
          fail();
        }
        break;
      }
      case 6:
        fprintf(f, "PATT\t%s", pats[l]);
        break;

      case BC_H_CALL: {
        using namespace BC_L_CALL_RUNTIME;
        switch (l) {
        case 0:
          fprintf(f, "CALL\tLread");
          push(call_runtime_function(Lread));
          break;

        case BC_L_WRITE: {
          fprintf(f, "CALL\tLwrite");
          push(call_runtime_function(Lwrite));
          break;
        }
        case BC_L_LENGTH:
          fprintf(f, "CALL\tLlength");
          push(call_runtime_function(Llength));
          break;

        case 3:
          fprintf(f, "CALL\tLstring");
          break;

        case BC_L_ARRAY: {
          int n = read_int();
          fprintf(f, "CALL\tBarray\t%d", n);
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

      fprintf(f, "\n");
    }
  stop:
    fprintf(f, "\n<end>\n");
  }
};

/* Dumps the contents of the file */
void dump_file (FILE *f, bytefile_ptr bf) {
  int i;
  
  fprintf (f, "String table size       : %d\n", bf->stringtab_size);
  fprintf (f, "Global area size        : %d\n", bf->global_area_size);
  fprintf (f, "Number of public symbols: %d\n", bf->public_symbols_number);
  fprintf (f, "Public symbols          :\n");

  for (i=0; i < bf->public_symbols_number; i++)
    fprintf(f, "   0x%.8x: %s\n", bf->get_public_offset(i),
            bf->get_public_name(i));

  fprintf (f, "Code:\n");
  Interpreter interp(std::move(bf));
  interp.interpret(f);
}

int main (int argc, char* argv[]) {
  auto f = read_file (argv[1]);
  dump_file (stderr, std::move(f));
  return 0;
}

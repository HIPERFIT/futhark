{-# LANGUAGE QuasiQuotes #-}
-- | C code for reading Futhark values from standard input.  Put here in
-- order not to clutter the main code generation module with a huge
-- block of C.
module Futhark.CodeGen.Backends.GenericC.Reading
  ( readerFunctions
  ) where

import qualified Language.C.Syntax as C
import qualified Language.C.Quote.C as C

-- | Defines the following functions parser function, all of which
-- read from standard input and return non-zero on error:
--
-- @
-- int read_array(typename int64_t elem_size, int (*elem_reader)(void*),
--                void **data, typename int64_t *shape, typename int64_t dims)
--
-- int read_int(void* dest)
--
-- int read_char(void* dest)
--
-- int read_double(void* dest)
--
-- int read_float(void* dest)
-- @
--
readerFunctions :: [C.Definition]
readerFunctions =
  [C.cunit|
    struct array_reader {
      char* elems;
      typename int64_t n_elems_space;
      typename int64_t elem_size;
      typename int64_t n_elems_used;
      typename int64_t *shape;
      int (*elem_reader)(void*);
    };

    int peekc() {
      int c = getchar();
      ungetc(c,stdin);
      return c;
    }

    int next_is_not_constituent() {
      int c = peekc();
      return c == EOF || !isalnum(c);
    }

    void skipspaces() {
      int c = getchar();
      if (isspace(c)) {
        skipspaces();
      } else if (c == '-' && peekc() == '-') {
        // Skip to end of line.
        for (; c != '\n' && c != EOF; c = getchar());
        // Next line may have more spaces.
        skipspaces();
      } else if (c != EOF) {
        ungetc(c, stdin);
      }
    }

    int read_elem(struct array_reader *reader) {
      int ret;
      if (reader->n_elems_used == reader->n_elems_space) {
        reader->n_elems_space *= 2;
        reader->elems=
          realloc(reader->elems,
                  reader->n_elems_space * reader->elem_size);
      }

      ret = reader->elem_reader(reader->elems + reader->n_elems_used * reader->elem_size);

      if (ret == 0) {
        reader->n_elems_used++;
      }

      return ret;
    }

    int read_array_elems(struct array_reader *reader, int dims) {
      int c;
      int ret;
      int first = 1;
      char *knows_dimsize = calloc(dims,sizeof(char));
      int cur_dim = dims-1;
      typename int64_t *elems_read_in_dim = calloc(dims,sizeof(int64_t));
      while (1) {
        skipspaces();

        c = getchar();
        if (c == ']') {
          if (knows_dimsize[cur_dim]) {
            if (reader->shape[cur_dim] != elems_read_in_dim[cur_dim]) {
              ret = 1;
              break;
            }
          } else {
            knows_dimsize[cur_dim] = 1;
            reader->shape[cur_dim] = elems_read_in_dim[cur_dim];
          }
          if (cur_dim == 0) {
            ret = 0;
            break;
          } else {
            cur_dim--;
            elems_read_in_dim[cur_dim]++;
          }
        } else if (c == ',') {
          skipspaces();
          c = getchar();
          if (c == '[') {
            if (cur_dim == dims - 1) {
              ret = 1;
              break;
            }
            first = 1;
            cur_dim++;
            elems_read_in_dim[cur_dim] = 0;
          } else if (cur_dim == dims - 1) {
            ungetc(c, stdin);
            ret = read_elem(reader);
            if (ret != 0) {
              break;
            }
            elems_read_in_dim[cur_dim]++;
          } else {
            ret = 1;
            break;
          }
        } else if (c == EOF) {
          ret = 1;
          break;
        } else if (first) {
          if (c == '[') {
            if (cur_dim == dims - 1) {
              ret = 1;
              break;
            }
            cur_dim++;
            elems_read_in_dim[cur_dim] = 0;
          } else {
            ungetc(c, stdin);
            ret = read_elem(reader);
            if (ret != 0) {
              break;
            }
            elems_read_in_dim[cur_dim]++;
            first = 0;
          }
        } else {
          ret = 1;
          break;
        }
      }

      free(knows_dimsize);
      free(elems_read_in_dim);
      return ret;
    }

    int read_array(typename int64_t elem_size, int (*elem_reader)(void*),
                   void **data, typename int64_t *shape, typename int64_t dims) {
      int ret;
      struct array_reader reader;
      typename int64_t read_dims = 0;
      while (1) {
        int c;
        skipspaces();
        c = getchar();
        if (c=='[') {
          read_dims++;
        } else {
          if (c != EOF) {
            ungetc(c, stdin);
          }
          break;
        }
      }

      if (read_dims != dims) {
        return 1;
      }

      reader.shape = shape;
      reader.n_elems_used = 0;
      reader.elem_size = elem_size;
      reader.n_elems_space = 16;
      reader.elems = calloc(elem_size, reader.n_elems_space);
      reader.elem_reader = elem_reader;

      ret = read_array_elems(&reader, dims);

      *data = reader.elems;

      return ret;
    }

    int read_int8(void* dest) {
      skipspaces();
      if (scanf("%hhi", (typename int8_t*)dest) == 1) {
        scanf("i8");
        return next_is_not_constituent() ? 0 : 1;
      } else {
        return 1;
      }
    }

    int read_int16(void* dest) {
      skipspaces();
      if (scanf("%hi", (typename int16_t*)dest) == 1) {
        scanf("i16");
        return next_is_not_constituent() ? 0 : 1;
      } else {
        return 1;
      }
    }

    int read_int32(void* dest) {
      skipspaces();
      if (scanf("%i", (typename int32_t*)dest) == 1) {
        scanf("i32");
        return next_is_not_constituent() ? 0 : 1;
      } else {
        return 1;
      }
    }

    int read_int64(void* dest) {
      skipspaces();
      if (scanf("%Li", (typename int64_t*)dest) == 1) {
        scanf("i64");
        return next_is_not_constituent() ? 0 : 1;
      } else {
        return 1;
      }
    }

    int read_char(void* dest) {
      skipspaces();
      if (scanf("%c", (char*)dest) == 1) {
        return 0;
      } else {
        return 1;
      }
    }

    int read_double(void* dest) {
      skipspaces();
      if (scanf("%lf", (double*)dest) == 1) {
        scanf("f64");
        return next_is_not_constituent() ? 0 : 1;
      } else {
        return 1;
      }
    }

    int read_float(void* dest) {
      skipspaces();
      if (scanf("%f", (float*)dest) == 1) {
        scanf("f32");
        return next_is_not_constituent() ? 0 : 1;
      } else {
        return 1;
      }
    }

    int read_bool(void* dest) {
      /* This is a monstrous hack.  Maybe we should get a proper lexer in here. */
      char b[4];
      skipspaces();
      if (scanf("%4c", b) == 1) {
        if (strncmp(b, "True", 4) == 0) {
          *(int*)dest = 1;
          return 0;
        } else if (strncmp(b, "Fals", 4) == 0 && getchar() == 'e') {
          *(int*)dest = 0;
          return 0;
        } else {
          return 1;
        }
      } else {
        return 1;
      }
    }
   |]

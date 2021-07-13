.. _js-api:

JavaScript API Reference
========================

The :ref:`futhark-wasm(1)` and :ref:`futhark-wasm-multicore(1)`
compilers produce JavaScript wrapper code to allow JavaScript programs
to invoke the generated WebAssembly code.  This chapter describes the
API exposed by the wrapper.

First a warning: **the JavaScript API is experimental**.  It may
change incompatibly even in minor versions of the compiler.

FutharkContext
--------------
FutharkContext is a class that contains information about the context
and configuration from the C API. It has methods for invoking the Futhark
entry points and creating FutharkArrays on the WebAssembly heap.


.. js:function:: constructor()

   Creates a new FutharkContext.

.. js:function:: free()

   Frees all memory created by the FutharkContext object. Should be called
   when the FutharkContext is done being used.

Values
------

Numeric types ``u8``, ``u16``, ``u32``, ``i8``, ``i16``, ``i32``, ``f32``,
and ``f64`` are mapped to JavaScript's standard number type. 64-bit integers
``u64``, and ``i64`` are mapped to  ``BigInt``. ``bool`` is mapped to
JavaScript's ``boolean`` type. Arrays are represented by the ``FutharkArray``.
complex types (records, nested tuples, etc) are represented by the
``FutharkOpaque`` class.

FutharkArray
------------
``FutharkArray`` has the following API

.. js:function:: toArray()

   Returns a nested JavaScript array

.. js:function:: toTypedArray()

   Returns a flat typed array of the underlying data.

.. js:function:: shape()

   returns the shape of the FutharkArray as an array of BigInts.

.. js:function:: free()

   Frees the memory used by the FutharkArray class

``FutharkContext`` also contains two functions for creating FutharkArrays
from JavaScript arrays, and typed arrays for each array type that appears
in an entry point.
All array types share similar API methods on the FutharkContext,
which is illustrated here forthe case of the type ``[]i32``.

.. js:function:: new_i32_1d_from_jsarray(jsarray)

  Creates and returns a one dimensional ``i32`` FutharkArray representing
  the JavaScript array jsarray

.. js:function:: new_i32_1d(array, dim1)

  Creates and returns a one dimensional ``i32`` FutharkArray representing
  the typed array of array, with the size given by dim1.


FutharkOpaque
-------------
complex types (records, nested tuples, etc) are represented by `FutharkOpaque``.
It has no use outside of being accepted and returned by
entry point functions. For this reason the method only has one function
for freeing the memory when ``FutharkOpaque`` is no longer used.

.. js:function:: free()

   Frees  memory used by FutharkOpaque. Should be called when Futhark
   Opaque is no longer used.

Entry Points
------------

Each entry point in the compiled futhark program has an entry point method on
the FutharkContext

.. js:function:: <entry_point_name>(in1, ..., inN)

  The entry point function taking the N arguments of the Futhark entry point
  function, and returns the result. If the result is a tuple the return value
  is an array.

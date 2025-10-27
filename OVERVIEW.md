Bauble is Rust-inspired human-readable text format for representing various Rust-like data, such as enums or structs.

Data represented by Bauble can be parsed and stored in memory in the form of a corresponding type on Rust which implements the [`Bauble`] trait.
In this way, Bauble is a format very useful for specifying information processed to Rust in a way that remains very consistent to the actual Rust code itself that makes use of the information.

Once a context has been created, that context can then be used for parsing various Bauble source files and extracting the newly parsed data back as typed values that can be used to update the state of the program.

# BaubleContext

[`BaubleContext`] is used to register various Bauble source files to parse information from, as well as maintaining a type registry where every known type to Bauble is provided.
Through [`BaubleContext`], various separate Bauble source files are able to reference each other's objects.
All interactions with Bauble require a context.

# Deriving Bauble

In order to represent a type inside of Bauble, you must implement the `Bauble` trait for that type.
To make this easier, Bauble has a custom derive macro `#[derive(Bauble)]`.

Here is a following example of using `#[derive(Bauble)]` to create a Bauble parsable type.
```
# use bauble::Bauble;

#[derive(Bauble)]
struct TypeInBauble {
   a_number: u32,
   a_string: String,
   a_bool: bool,
}
```

More information on the [`Bauble`] derive macro exists in its documentation.

# Getting started with using Bauble

In order to use Bauble, the first step is to create a [`BaubleContext`].
The [`BaubleContext`] can be created via a [`BaubleContextBuilder`].
With the builder you may register various types and traits.
The types and traits you provide to the builder can then be used to create values in Bauble which are associated with those types you registered from Rust.
For example, if you create a struct in Rust that represents a person `struct Person { name: String, age: u32 }`, that struct can then be written out in Bauble like `person = Person { name: "Maria", age: 21 }`, or, `person: Person = Person { name: "David", age: 35 }`.
In order to register a trait, the builder expects a type in the form of `dyn Trait`.
More on [traits below](#traits).
The builder is also capable of doing various other things like registering preludes (implicitly used types) or a required trait for all types, amongst others.
Note, in order for Bauble to recognize a type as implementing a specific trait, it has to be registered manually to the builder at this stage.
Once you've registered all your types and traits to the builder, you can build the context.

Once you have your context, it can be used to register Bauble source files using [`BaubleContext::register_file`].
These will be parsed by the context when you invoke [`BaubleContext::load_all`].
[`BaubleContext::load_all`] returns all Bauble 'objects' that were parsed, as well as any potential errors that occured when parsing the Bauble source.
A Bauble object is a typed lexical element of Bauble.
A Bauble object can be converted into a concrete value of type `T` that implements [`Bauble`] by passing the inner value to [`Bauble::from_bauble`].
Whether the conversion is successful depends on the implementation of the [`Bauble`] trait on the type `T`.
In order to support all Bauble values being parsed and represented as a single type in Rust, using type erasure is a possibility, however it has to be manually implemented.
For example, a single `ErasedBauble` type which can represent any type that implements `Bauble`, but has to be explicitly downcast to the concrete type sometime later at runtime (when the type is known).  

## Bauble overview

# Includes (use)

All Bauble source files support the usage of `use`.
Similar to Rust, it may include any item defined from a separate Bauble module, as long as both modules (the module being used, and the module using) exist within the same [`BaubleContext`].
Alternatively to `use`, like in Rust, the fully qualified path may be written out instead.
`use` may be used to include both objects and Bauble registered types/traits.

# Object

All bauble source files consists of a set of objets.
A single Bauble object is a tree of Bauble values and a type.
A Bauble object can be thought of as a single asset, being tied to a unique path.
Objects are the format of its contents Bauble provides after it has parsed all of its files, and ultimately what is used to convery the parsed Bauble contents. 

# Values

 A value in Bauble is typed, and contains an enum representing the kind of the value (whether it is a number, a string, an array or a map for example).
Values are not that usually interacted with by the end user, as generally Bauble is implemented through the derive macro which means the user does not need to handle parsing from a raw Bauble value themselves.

# Types

Types are registered to the [`BaubleContext`] through the builder, and every type requires the [`Bauble`] trait to be implemented on top of it.
The [`Bauble`] trait determines how the type gets registered into the [`BaubleContext`], how it is parsed from Bauble source, and what path the type has.
In Bauble every object is associated with a type, the type may be explicitly written with the value or implied by context, similar to type inference rules in Rust.

# Traits

Traits may be registered to Bauble in the form of `dyn Trait` types.
If a trait has been registered, `dyn Trait` can then be used within registered Bauble types. In order for Bauble to parse a value of type `dyn Trait` with a value of a type that implements `Trait` called `T`, both `Trait` the `T` must be registered, and Bauble must know `T` implements `Trait`.
Every trait implementation you want Bauble to know about must be explicitly registered.
Bauble is unable to use reflection and figure out if a type implements a trait based purely on if it implements that trait in Rust, which is an unfortunate limitation.
In order to register Bauble traits, you can use the method [`get_or_register_trait`](types::TypeRegistry::get_or_register_trait), then in order to mark a type as implementing that trait in Bauble,
use [`add_trait_dependency`](types::TypeRegistry::add_trait_dependency)

# Modules

Every registered source file in Bauble is a module, similar to Rust. Every module contains various assets. The notion of sub-modules are not really present in Bauble.

# Paths

Every asset, module, reference and registered type/trait in Bauble has a corresponding unique path. In Bauble this is known as [`path::TypePath`], and is the association to that particular element in the [`BaubleContext`].
A path consists of various elements. Similar to Rust, most elements are seperated by `::`, so `a::b` means element `b` which is a child of element `a`.
An element here can be a module, type or object.
There are things known as sub-objects which may be appended to the path of a regular object, which are effectively children of the current object.
A sub-object's path is denoted by `<path to parent>&$ty@$idx` where `$ty` is the index of the type of the sub-object and `$idx` is the index of the sub-object to the parent (the first sub-oject being 0, the second 1, the third 2, etc).

# References

A reference is a Bauble object which may not be present in the current module.
A Bauble object's value may use a reference to avoid code duplication in the local file (referencing a previous object to use its values), or to reference the value of a Bauble object from a different file (module).
References are specified using a bauble `Path`.

Bauble does expose the builtin type for references, [`Ref`], which can be used for convenience to represent references from Bauble in Rust.
It is not required to use this type to represent references, custom types which are capable of parsing reference values are equal to the builtin [`Ref`] type, it is just a convenience.

# Sub-objects

A single Bauble object may contain sub-objects.
A sub-object is a reference value within a Bauble object which is not written as a reference, and rather as an "inlined" object directly defined together with the object.
Functionally sub-objects work similar to a regular reference with the difference being they are defined locally to the object where they are used and are not
top level objects themselves.

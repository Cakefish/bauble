use bauble_macro_util::derive_bauble;
use proc_macro::TokenStream;

/// Derive `Bauble`, allowing you to construct a rust type from a bauble object.
///
/// This type will also need to be registered on the bauble context with
/// `BaubleContextBuilder::register_type` to be able to parse this type in bauble.
///
/// # Only type attributes
///
/// Attributes that can be added to the type, i.e above enum or struct.
///
/// - `path`: Changes the module for this in the bauble type system.
/// - `traits`: Adds traits which this type implements to the bauble trait.
/// - `allocator`: Changes what allocator that is used, by default this is
///   `DefaultAllocator`.
/// - `bounds`: Adds extra bounds to the `Bauble` implementation.
/// - `from`: Parse this type as if it was flattening to the specified type.
///   Specified like `from = T` and this type has to implement `From<T>`.
///
/// # Container or type attributes
///
/// Attributes that can be added to a type or enum variant.
///
/// - `extra`: Adds extra key, string data to the bauble type.
/// - `rename`: Renames the identifier used in the bauble type system.
/// - `flatten`: If there is only one field in the container this container will
///   be deserialized from that type. If this is on a tuple struct or variant with
///   more than one field, it will be deserialized from a tuple. If this is on an
///   enum, it's the same as if all the variants had the `flatten` attribute.
/// - `validate`: Adds extra validation to this type or variant. Expects a function
///   like `fn(&Val, &TypeRegistry) -> Result<(), ConversionError>`. Can either
///   be a defined function, or a closure.
/// - `value_default`: Used to give the bauble type a default.
///
/// # Only container attributes
///
/// Attributes that can be added to the container, i.e above struct or enum
/// variants.
///
/// - `tuple`: Converts a struct or variant with named fields to be parsed as a
///   struct or variant with unnamed fields.
///
/// # Field attributes:
///
/// Attributes that can be added to fields, in both structs and enum variants.
///
/// - `extra`: Adds extra key, string data to this field.
/// - `as_default`: Always sets this field to a default value, bauble won't know
///   this field exists. Can have `as_default = <value>` to assign to a specific
///   default. If nothing is assigned uses `Default::default`.
/// - `default`: If the field isn't present in bauble, sets it to a defualt value.
///   Can have `default = <value>` to assign to a specific default. If nothing is
///   assigned uses `Default::default`.
/// - `attribute`: This field is instead deserialized from bauble attributes. By
///   doing `attribute = <ident>` it can be assigned to read from a specific
///   attribute. By default it uses the field's name.
/// - `value_default`: Used to give the field type a default in the bauble type system.
#[proc_macro_derive(Bauble, attributes(bauble))]
pub fn derive(input: TokenStream) -> TokenStream {
    derive_bauble(input.into()).into()
}

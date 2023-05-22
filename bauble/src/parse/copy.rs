use indexmap::IndexMap;

use crate::parse::PathEnd;

use super::{Ident, Object, Value};

// TEMP
pub fn copy(values: Vec<&mut Value>, copies: &IndexMap<Ident, Object>) {
    use Value::*;

    for value in values {
        if let Some(reference) = match value {
            Unit | Num(_) | Bool(_) | Str(_) | Path(_) | Or(_) | Raw(_) | Error => None,
            Ref(reference) => Some(&*reference),
            Struct { fields, .. } => {
                copy(
                    fields
                        .values_mut()
                        .map(|object| &mut object.value.value)
                        .collect(),
                    copies,
                );
                None
            }
            Tuple {
                fields: sequence, ..
            }
            | Array(sequence) => {
                copy(
                    sequence
                        .iter_mut()
                        .map(|object| &mut object.value.value)
                        .collect(),
                    copies,
                );
                None
            }
            Map(map) => {
                copy(
                    map.iter_mut()
                        .flat_map(|(key, value)| [&mut key.value.value, &mut value.value.value])
                        .collect(),
                    copies,
                );
                None
            }
        } {
            if !reference.leading.is_empty() {
                continue;
            }

            let PathEnd::Ident(ident) = &reference.last.value else { continue };

            if let Some(object) = copies.get(ident.as_str()) {
                *value = (*object.value).clone();
            }
        }
    }
}

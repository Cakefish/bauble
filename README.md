# Bauble

Bauble is a data format targeted at games with rust-like syntax.

It is intended to be used with a system that has some kind of reflection on types. So types can be optionally included instead of refering to them by full path. And it also gives the data-format the potential to load erased types.

Bauble has three steps in parsing.
1. text -> simple intermediate data representation. 
2. -> intermediate data representation with resolved types.
3. -> rust types through implementation of `FromBauble`. 

## Examples of bauble
```rust
// bauble has the capability to use different types. Which are resolved by the `AssetCtx`
use rpg::{Enemy, DamageType};

slime = Enemy {
  name: "Slime",
  hp: 200,
  speed: 2.5,
  damage_type: DamageType::Slimy,
  // Arrays, which could be deserialized as other containers, are deliminated by `[]`
  attacks: [$slam_attack],
}

// Putting `copy` infront of a definition essentially makes it a macro.
// As in rust, tuples are delimeted by `()`.
copy slam_attack = (2.5, "Slam")
```

Bauble also supports a raw piece of data, that could potentially be used for code. Raw values need to be defined how to be handled when they are converted to rust types.
```rust
use rpg::{Ability, Projectile, OnUse};
fireball = Ability {
  name: "Fireball",
  // You can link to assets by prefixing a path with `$`.
  audio: $assets::sounds::fireball_audio,
  // You can link to other assets within the document.
  on_use: OnUse::SpawnProjectile($fireball_projectile),
}

fireball_projectile = Projectile {
  // After a `#` a raw value is accepted. This could be used for a color.
  color: #42f56f,
  // Or a dice roll.
  hit_damage: #2d6,
  // Everything within #{ ... } is considered raw data. Other instances of `{` must be delimited by `}`.
  on_hit: #{
    ctx.spawn_effect("FireballEffect");
    ctx.play_sound("FireballSound");
    for enemy in ctx.nearby_enemies(1.0) {
      enemy.damage(ctx.data.hit_damage);
    }
  }
}
```

For just a raw value after `#`, the following characters are accepted:
 - Special char acters: `!`, `#`, `@`, `%`, `&`, `?`, `.`, `=`, `<`, `>`, `_`, `-`, `+`, `*`
 - Alphabetical numerical characters, see (is_alphanumeric)[https://doc.rust-lang.org/std/primitive.char.html#method.is_alphanumeric].

There is no specific reason this list can't be expanded.

Various other types:

```rust
use rpg::{Creature, Capability};

human = Creature {
  // A map is delimitered by `{}`, and uses the syntax `key: value`
  body_parts: {
    // A list of paths seperated by `|`, could potentially be parsed to bitfields or something like `EnumSet`.
    "head": Capability::Sight | Capability::Hearing | Capability::Smell,
    "arms": Capability::Interact | Capability::Swim,
    "legs": Capability::Walk | Capability::Jump,
  }
}
```

Using attributes can be useful to add extra information to objects. Although the parsing for this needs to be manually defined.
```rust
use ui::{Button, Node}
canvas = #[width = Fill, height: Fill] Node {
  children: [
    #[width = 100, height = 100] Button {
      on_press: #{ println!("Hello") },
    },
    #[width = 100, height = 100] Button {
      on_press: #{ println!("World") },
    },
  ]
}
```
Attributes support a binding equals an expression, i.e `ident = anything_goes_here`. And supports both comma separation and multiple attributes on the same item.

## Using a custom allocator

Bauble has the capability to use a custom allocator through the `BaubleAllocator` trait. With this you can for example allocate values within an arena.
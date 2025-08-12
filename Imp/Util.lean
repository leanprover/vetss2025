-- Anticipating changes not yet in this release
@[grind] theorem bind_eq_bind {α β : Type} (x : Option α) (f : α → Option β) : x >>= f = Option.bind x f :=
  rfl

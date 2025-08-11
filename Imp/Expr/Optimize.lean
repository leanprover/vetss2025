import Imp.Expr.Basic
import Imp.Expr.Eval

namespace Imp.Expr

/--
Optimizes an expression by folding constants.
-/
def optimize : Expr → Expr
  | .const i => .const i
  | .var x => .var x
  | .op bop e1 e2 =>
    match optimize e1, optimize e2 with
    | .const i, .const i' =>
      if let some v := bop.apply i i' then .const v
      else .op bop (.const i) (.const i')
    | e1', e2' => .op bop e1' e2'

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e <;> simp [optimize]
  case op bop e1 e2 ih1 ih2 =>
    split <;> simp [eval, *]
    split
    · simp [eval, *]
    · simp [eval]

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok' (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e using optimize.induct <;> simp [eval, optimize, *]

-- Anticipating changes not yet in this release
set_option grind.warning false
@[grind] theorem bind_eq_bind {α β : Type} (x : Option α) (f : α → Option β) : x >>= f = Option.bind x f :=
  rfl

theorem optimize_ok'' (e : Expr) : e.optimize.eval σ = e.eval σ := by
  induction e using optimize.induct <;> grind [eval, optimize]

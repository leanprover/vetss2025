import Imp.Stmt.BigStep

namespace Imp

namespace Stmt

/--
Lean allows possibly non-terminating functions if they are in the `Option` monad, so that
nontermination can be logically modelled as returning `Option.none`. This kind of partial
function definition needs to be explicitly enabled using `partial_fixpoint`.
-/
def run (σ : Env) (s : Stmt) : Option Env :=
  match s with
  | imp {skip;} =>
    some σ
  | imp {~s1 ~s2} => do
    let σ' ← run σ s1
    run σ' s2
  | imp {~x := ~e;} => do
    let v ← e.eval σ
    pure (σ.set x v)
  | imp {if (~c) {~s1} else {~s2}} => do
    let v ← c.eval σ
    if v = 0 then
      run σ s2
    else
      run σ s1
  | imp {while (~c) {~s1}} => do
    let v ← c.eval σ
    if v = 0 then
      pure σ
    else
      let σ' ← run σ s1
      run σ' (imp {while (~c) {~s1}})
partial_fixpoint

/-- info: 3628800 -/
#guard_msgs in
#eval ((run (Env.init 0 |>.set "n" 10) fact).get!.get "out").toNat

example : run σ (imp {skip;}) = some σ := by
  simp [run]

/--
`run` is partially correct: if it returns an answer, then that final state can be reached by the
big-step semantics.

Note that this is not total correctness - `run` could always return `none` and still satisfy this
theorem.
-/
theorem run_some_implies_big_step : run σ s = some σ' → BigStep σ s σ' := by
  apply run.partial_correctness
  intro run ih σ s σ' heq
  split at heq <;> simp_all
  · simp [Option.bind_eq_some_iff] at heq
    obtain ⟨σ'', heq1, heq2⟩ := heq
    have := ih _ _ _ heq1
    have := ih _ _ _ heq2
    constructor <;> assumption
  · simp [Option.bind_eq_some_iff] at heq
    obtain ⟨σ'', heq1, heq2⟩ := heq
    subst heq2
    constructor <;> assumption
  · simp [Option.bind_eq_some_iff] at heq
    obtain ⟨v, heq1, heq2⟩ := heq
    split at heq2
    · apply BigStep.ifFalse <;> simp_all
    · apply BigStep.ifTrue (v := v) <;> simp_all
  · simp [Option.bind_eq_some_iff] at heq
    obtain ⟨v, heq1, heq2⟩ := heq
    split at heq2
    · simp at heq2; subst heq2
      apply BigStep.whileFalse <;> simp_all
    · simp [Option.bind_eq_some_iff] at heq2
      obtain ⟨σ'', heq2, heq3⟩ := heq2
      have := ih _ _ _ heq2
      have := ih _ _ _ heq3
      apply BigStep.whileTrue (v := v) <;> assumption

/--
To complete correctness, we prove that if the program has semantics wrt to the big-step-semantics,
then `run` returns (with the right result).
-/
theorem big_step_implies_run_some (h : BigStep σ s σ') : run σ s = some σ':= by
  induction h
  all_goals try solve | simp [run, *]
  case «whileTrue» v σ''' body σ' c σ'' hc hnn _ _ ih1 ih2 =>
    rw [run] -- simp [run] would loop here, so use `rw`
    simp [*]
  case «whileFalse» h =>
    rw [run]
    simp [*]

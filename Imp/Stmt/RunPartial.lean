import Imp.Stmt.BigStep

namespace Imp

namespace Stmt

/--
A variant of run using `partial_fixpoint`
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
`run` is correct: if it returns an answer, then that final state can be reached by the big-step
semantics. This is not total correctness - `run` could always return `none` - but it does increase
confidence.
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
The other direction: If the program has semantics wrt to the big-step-semantics, then `run`
returns the right result.
-/
theorem big_step_implies_run_some (h : BigStep σ s σ') : run σ s = some σ':= by
  induction h
  all_goals try solve | simp_all [run]
  case «whileTrue» v σ''' body σ' c σ'' hc hnn _ _ ih1 ih2 =>
    rw [run]
    simp [hc, *]
  case «whileFalse» h =>
    rw [run]
    simp [h]

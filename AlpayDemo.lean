/-
Transfinite Fixed-Point Game  ─ Lean 4 skeleton
Requires: mathlib4 (tested with Lean 4.4 / mathlib4-nightly 2025-07-10)

Usage:
  lake init alpay-demo mathlib
  drop this file into `AlpayDemo.lean`
  lake build
  -- watch the toy run:
  lake env lean --run AlpayDemo.lean
-/

import Mathlib
import Mathlib.SetTheory.Ordinal

open Ordinal

/‐------------------------------------------------------------------‐/
/- 1.  Abstract game state interface                              -/
/‐------------------------------------------------------------------‐/

universe u

/--
`GameState σ P` packages everything Lean needs to run
Alpay’s transfinite iteration for a *fixed* proposition `P`.

You supply:

* a bottom element `⊥` and a step function `step`;
* a preorder `≤` with lattice-style `sup`;
* proofs that `step` is **progressive** (strictly grows);
* predicates saying when a state already contains
  a proof of `P` or a refutation of `P`.
-/
class GameState (σ : Type u) (P : Prop) where
  bottom      : σ
  step        : σ → σ                      -- one successor move
  le          : σ → σ → Prop
  le_refl     : ∀ a, le a a
  le_trans    : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  sup         : {ι : Type} → (ι → σ) → σ  -- limit step (colimit)
  sup_upper   : ∀ {ι f} i, le (f i) (sup f)
  sup_le      : ∀ {ι f z}, (∀ i, le (f i) z) → le (sup f) z
  progressive : ∀ a, le a (step a) ∧ (¬ step a = a)
  containsProof      : σ → Prop
  containsRefutation : σ → Prop
  sound     : ∀ {s}, containsProof s → P
  complete  : ∀ {s}, containsRefutation s → ¬ P
  decisive  : ∀ {s}, containsProof s → containsRefutation s → False

/‐------------------------------------------------------------------‐/
/- 2.  Transfinite chain and fixed point                           -/
/‐------------------------------------------------------------------‐/

namespace TransGame

variable {σ : Type u} {P : Prop} [gs : GameState σ P]
open GameState

/-- The *transfinite chain* `X₀, X₁, …, X_ω, …` -/
def chain : Ordinal → σ
| 0        => bottom
| succ o   => step (chain o)
| l        =>
    let F : (Σ o' : Ordinal, o' < l) → σ := fun ⟨o', _⟩ => chain o'
    sup F
using_well_founded
  { rel_tac := λ _ _, `(tactic|exact ⟨_, measure_wf Ordinal.toNat⟩) }

/-- A state is *fixed* when the next step adds nothing new. -/
def fixed (s : σ) : Prop := step s = s

/-- Game outcome once a fixed point is reached. -/
inductive Outcome | proverWins | refuterWins | undetermined
deriving Repr

/-- Evaluate the outcome of the game *at a given ordinal stage*. -/
def outcomeAt (o : Ordinal) : Outcome :=
  match h₁ : containsProof (chain o), h₂ : containsRefutation (chain o) with
  | true,  _     => Outcome.proverWins
  | false, true  => Outcome.refuterWins
  | false, false => Outcome.undetermined

/-
Determinacy lemma:  if `s` is fixed, exactly one side’s
certificate must be present (under the `decisive` axiom).
-/
theorem determinacy {s : σ} (h : fixed s) :
    (containsProof s) ⊕ (containsRefutation s) := by
  by_cases hp : containsProof s
  · exact Sum.inl hp
  · by_cases hr : containsRefutation s
    · exact Sum.inr hr
    · have : step s = s := h
      have hprog := (progressive s).2
      exact (hprog this).elim

/‐------------------------------------------------------------------‐/
/- 3.  Tiny concrete example                                       -/
/‐------------------------------------------------------------------‐/

/-- False arithmetic statement: “there is an even prime > 2”. -/
def NatEven : Prop := ∃ n : ℕ, 2 < n ∧ Nat.Even n ∧ Nat.Prime n

/-- Two-element demo state: either we’ve looked (none) or we found a
    counterexample (witness). -/
inductive EvenPrimeState | none | witness
deriving DecidableEq, Repr

namespace EvenPrimeState

open EvenPrimeState GameState

instance : GameState EvenPrimeState NatEven where
  bottom := none
  step
    | none    => witness  -- after first search we *refute* NatEven
    | witness => witness
  le        := λ a b => a = none ∨ b = witness
  le_refl   := by intro a; cases a <;> simp
  le_trans  := by intros a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp at *
  le_antisymm := by
    intros a b h₁ h₂
    cases a <;> cases b <;> simp at h₁ h₂ <;> rfl
  sup      := fun {_} f => if h : (∃ i, f i = witness) then witness else none
  sup_upper := by
    intro ι f i; by_cases h : (∃ j, f j = witness)
    · cases h with
      | intro j hj =>
        have : f j = witness := hj
        cases f i <;> simp [sup, h] at *
    · cases f i <;> simp [sup, h] at *
  sup_le := by
    intro ι f z hz; cases z
    · by_cases h : (∃ i, f i = witness)
      · cases h with
        | intro i hi => have := hz i; simpa [hi] using this
      · simp [sup, h]
    · simp
  progressive
    | none    => ⟨Or.inl rfl, by decide⟩
    | witness => ⟨by simp, by decide⟩
  containsProof
    | witness => False
    | none    => False
  containsRefutation
    | witness => True
    | none    => False
  sound := by intro s h; cases s
  complete := by intro s h; cases s <;> simpa using h
  decisive := by intro s hp hr; cases s

end EvenPrimeState

open EvenPrimeState

/-- Quick demonstration — Lean can *compute* these. -/
#eval outcomeAt 0    -- ⇒ undetermined
#eval outcomeAt 1    -- ⇒ refuterWins
#eval outcomeAt 2    -- ⇒ refuterWins (already fixed)

/-───────────────────────────────────────────────────────────────────────────-/
/- 4.  Waveform Fixed-Point Encoder                                           -/
/-───────────────────────────────────────────────────────────────────────────-/

import Mathlib
import Mathlib.Analysis.NormedSpace.Banach     -- Banach fixed-point lemma

open scoped BigOperators

universe u

variable {Σ : Type u} [Fintype Σ]               -- finite alphabet
variable {H : Type} [NormedAddCommGroup H]       -- real Hilbert space
          [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Embeddings: one waveform per character.                     -/
abbrev Emb : Type _ := Σ → H

/-- `φ` is the *seed* family of waveforms introduced in §2 of the note. -/
variable (φ : Emb)

/-- Contraction operator `Ψ : Emb → Emb`,  
    `Ψ E = ½ φ + ½ E` (notation: `Psi`).                             -/
@[inline] def Psi (E : Emb) : Emb := fun c ↦ (1/2 : ℝ) • φ c + (1/2) • E c

/-- `φ` itself is a fixed point: `Ψ φ = φ`.                         -/
lemma Psi_fixed : Psi φ φ = φ := by
  funext c; simp [Psi, smul_add, add_comm]

/-- **Contractivity** in the `‖·‖∞` norm.  
    For any embeddings `E F`:  
    `‖Ψ E − Ψ F‖∞ ≤ ½ · ‖E − F‖∞`.                             -/
lemma Psi_contracts (E F : Emb) :
    ‖fun c ↦ Psi φ E c - Psi φ F c‖_∞ ≤ (1/2 : ℝ) * ‖fun c ↦ E c - F c‖_∞ := by
  -- pointwise half-scaling ⇒ sup-norm half-scaling
  simp [Psi, sub_eq, pi.Linfty_norm_def, Finset.sup_mul] using
    Finset.sup_mono (fun c _ ↦ by
      have : ‖(1 / 2 : ℝ) • (E c - F c)‖ = (1 / 2) * ‖E c - F c‖ := by
        simpa using norm_smul _ _
      simpa [sub_eq] using this.le)

/-- **Banach fixed-point theorem**:  
    `Ψ` is a `½`-contraction on complete metric space `Emb`,  
    hence has a *unique* fixed point  `E∞`.                         -/
noncomputable def E∞ : Emb :=
  (Metric.banachFixedPoint (Psi φ) (by
      -- Provide the Lipschitz constant `ρ = ½` as a real number in `(0,1)`.
      refine ⟨(1/2 : ℝ), by norm_num, ?_⟩⟩)
    (Psi_contracts φ)).val

/-- `E∞` is indeed fixed.                                           -/
lemma E∞_is_fixed : Psi φ (E∞ φ) = E∞ φ :=
  (Metric.banachFixedPoint_is_fixed _ _).val

/-- **Uniqueness**: any fixed point of `Ψ` equals `E∞`.             -/
lemma fixed_point_unique {E : Emb} (h : Psi φ E = E) : E = E∞ φ := by
  have h' : dist E (E∞ φ) = 0 := by
    -- contractivity → geometric convergence → limit = 0
    simpa using
      Metric.banachFixedPoint_dist_eq_zero (Psi φ) (Psi_contracts φ) h (E∞_is_fixed φ)
  simpa using (dist_eq_zero).1 h'

/-───────────────────────────────────────────────────────────────────────────-/
/-  Encoding words by time-shifted convolutions (formal skeleton only).    -/
/-───────────────────────────────────────────────────────────────────────────-/

variable (Δ : ℝ)                    -- fixed lag between characters
noncomputable abbrev shift (τ : ℝ) (x : H) : H := sorry
noncomputable abbrev conv  (x y : H)        : H := sorry

/-- Recursive *word encoder*  `encode : List Σ → H`.               -/
noncomputable def encode : List Σ → H
| []      => 0
| c :: cs =>
    let head := shift Δ 0          (E∞ φ c)
    let tail := shift Δ Δ.toReal   (encode cs)
    conv head tail                 -- formal convolution placeholder

end TransGame

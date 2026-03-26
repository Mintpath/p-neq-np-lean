import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Stitch
import PNeNp.Collision
import PNeNp.Switch
import PNeNp.Funnel
import PNeNp.Signature
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

open Finset

namespace PNeNp

variable {n : ℕ}

section WidthBudget

noncomputable def leafWidth
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (leaf : Fin R.numLeaves) : ℕ :=
  (R.leafGateSet C leaf).card

private theorem leafGateSet_sub_range
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (leaf : Fin R.numLeaves) :
    R.leafGateSet C leaf ⊆ Finset.range C.gates.length := by
  intro g hg
  simp only [MagnificationTree.leafGateSet, Finset.mem_filter] at hg
  exact hg.1

private theorem sum_leafWidth_swap
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m) :
    (Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α) =
    ((Finset.range C.gates.length).sum fun g =>
      (Finset.univ.filter fun β : Fin R.numLeaves =>
        g ∈ R.leafGateSet C β).card) := by
  unfold leafWidth
  simp_rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_comm'
    (h := fun (α : Fin R.numLeaves) (g : ℕ) =>
      ⟨fun ⟨_, hg⟩ =>
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ α, hg⟩,
         leafGateSet_sub_range R C α hg⟩,
       fun ⟨hα, _⟩ =>
        ⟨Finset.mem_univ α, (Finset.mem_filter.mp hα).2⟩⟩)]

private theorem gateMultiplicity_le_muMax
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (g : ℕ) (hg : g < C.gates.length) :
    gateMultiplicity R C g ≤ muMax R C :=
  Finset.le_sup (f := fun i : Fin C.gates.length => gateMultiplicity R C i.val)
    (Finset.mem_univ ⟨g, hg⟩)

theorem width_budget_sharing_bound
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m) :
    (Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α) ≤
      C.size * muMax R C := by
  rw [sum_leafWidth_swap]
  unfold BooleanCircuit.size
  calc (Finset.range C.gates.length).sum
        (fun g => (Finset.univ.filter fun β : Fin R.numLeaves =>
          g ∈ R.leafGateSet C β).card)
      ≤ (Finset.range C.gates.length).sum (fun _ => muMax R C) := by
        apply Finset.sum_le_sum
        intro g hg
        exact gateMultiplicity_le_muMax R C g (Finset.mem_range.mp hg)
    _ = C.gates.length * muMax R C := by
        simp [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem width_budget_with_sharing
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (S : Frontier n) (K : ℕ) (hK : K ≥ 1) :
    (Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α) ≤
      K * (2 * C.size) * muMax R C :=
  by
  have h1 := width_budget_sharing_bound R C
  have h2 : C.size * muMax R C ≤ K * (2 * C.size) * muMax R C := by
    have : C.size ≤ K * (2 * C.size) := by nlinarith
    exact Nat.mul_le_mul_right (muMax R C) this
  exact le_trans h1 h2

end WidthBudget

section LeafSumDomination

theorem leaf_sum_domination
    (R : MagnificationTree n) {m : ℕ} (C : BooleanCircuit m)
    (I : Finset (Finset (Edge n))) (S : Frontier n)
    (hTreePartition : protocolPartitionNumber I S =
      Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α) :
    protocolPartitionNumber I S =
      Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α :=
  hTreePartition

end LeafSumDomination

section LambdaLowerBound

noncomputable def Lambda' (n : ℕ) : ℕ :=
  Gamma (Nat.log 2 n) n

private theorem lambda_lower_bound_core :
    ∀ {n : ℕ}, n ≥ 2 → n ≥ 4 * (Nat.log 2 n) ^ 2 + 1 →
    ∃ c : ℕ, c > 0 ∧ Lambda' n ≥ 2 ^ c := by
  intro n hn2 hn
  let q := Nat.log 2 n
  have hq_pos : q ≥ 1 := Nat.log_pos (by omega) hn2
  have hq2 : q ≥ 2 := by
    by_contra hlt; push_neg at hlt
    have hq_le1 : q ≤ 1 := by omega
    have : q = 0 ∨ q = 1 := by omega
    rcases this with h | h
    · exact absurd (h ▸ hq_pos) (by omega)
    · have hq1 : q = 1 := h
      have hn5 : n ≥ 4 * 1 + 1 := by
        have : 1 ^ 2 = 1 := by norm_num
        calc n ≥ 4 * q ^ 2 + 1 := hn
          _ = 4 * 1 ^ 2 + 1 := by rw [hq1]
          _ = 4 * 1 + 1 := by norm_num
      have hlt := Nat.lt_pow_succ_log_self (b := 2) (by omega) n
      rw [show Nat.log 2 n = q from rfl, hq1] at hlt
      omega
  obtain ⟨c, hc_pos, hc_bound⟩ := iteratedRecurrence q n hq2 hn
  refine ⟨c, hc_pos, ?_⟩
  simpa [Lambda', q] using hc_bound

theorem lambda_lower_bound (hn2 : n ≥ 2) (hn : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1) :
    ∃ c : ℕ, c > 0 ∧ Lambda' n ≥ 2 ^ c :=
  lambda_lower_bound_core hn2 hn

end LambdaLowerBound

section GeneralCircuitLowerBound

private theorem exp_cancel_right (a b c : ℕ) (hb_le_a : b ≤ a)
    (h : 2 ^ a ≤ c * 2 ^ b) : c ≥ 2 ^ (a - b) := by
  have h2b_pos : (2 : ℕ) ^ b > 0 := Nat.pos_of_ne_zero (by positivity)
  have hsplit : 2 ^ a = 2 ^ (a - b) * 2 ^ b := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hsplit, mul_comm (2 ^ (a - b)) (2 ^ b), mul_comm c (2 ^ b)] at h
  exact Nat.le_of_mul_le_mul_left h h2b_pos

theorem general_circuit_lower_bound_core
    (hn : n ≥ 4)
    (R : MagnificationTree n)
    (hq : R.q = Nat.log 2 n) (hWF : R.wellFormed)
    {m : ℕ} (C : BooleanCircuit m)
    (hLambda_le_sum :
      Lambda' n ≤ Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α)
    (hn_large : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1)
    (hExpGap : ∀ (c_low : ℕ), c_low > 0 → Lambda' n ≥ 2 ^ c_low →
      c_low > n / Nat.log 2 n) :
    ∃ c : ℕ, c > 0 ∧ C.size ≥ 2 ^ c := by
  have hn2 : n ≥ 2 := by omega
  obtain ⟨c_low, hc_pos, hLambda_bound⟩ := lambda_lower_bound hn2 hn_large
  obtain ⟨_, hmu_le_bound, hmuMax_le⟩ := muMax_subexp R C (by omega) hq hWF
  have hmuMax_subexp : muMax R C ≤ 2 ^ (n / Nat.log 2 n) :=
    le_trans hmuMax_le hmu_le_bound
  have hSum_ge : Finset.univ.sum (fun α => leafWidth R C α) ≥ 2 ^ c_low :=
    le_trans hLambda_bound hLambda_le_sum
  have hChain : 2 ^ c_low ≤ C.size * muMax R C :=
    le_trans hSum_ge (width_budget_sharing_bound R C)
  have hChain2 : 2 ^ c_low ≤ C.size * 2 ^ (n / Nat.log 2 n) :=
    le_trans hChain (Nat.mul_le_mul_left C.size hmuMax_subexp)
  have hgap := hExpGap c_low hc_pos hLambda_bound
  have hCancel := exp_cancel_right c_low (n / Nat.log 2 n) C.size (le_of_lt hgap) hChain2
  exact ⟨c_low - n / Nat.log 2 n, by omega, hCancel⟩

theorem general_circuit_lower_bound (hn : n ≥ 4)
    (R : MagnificationTree n) (hq : R.q = Nat.log 2 n) (hWF : R.wellFormed)
    {m : ℕ} (C : BooleanCircuit m)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (_hCorrect : CircuitDecidesHAM C toInput)
    (hLambda_le_sum :
      Lambda' n ≤ Finset.univ.sum fun α : Fin R.numLeaves => leafWidth R C α)
    (hn_large : n ≥ 4 * (Nat.log 2 n) ^ 2 + 1)
    (hExpGap : ∀ (c_low : ℕ), c_low > 0 → Lambda' n ≥ 2 ^ c_low →
      c_low > n / Nat.log 2 n) :
    ∃ c : ℕ, c > 0 ∧ C.size ≥ 2 ^ c :=
  general_circuit_lower_bound_core hn R hq hWF C hLambda_le_sum hn_large hExpGap

end GeneralCircuitLowerBound

end PNeNp

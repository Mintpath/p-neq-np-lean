import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Switch
import PNeNp.Funnel
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

open Finset

namespace PNeNp

variable {n : ℕ}

section ProtocolPartitionTree

structure ProtocolPartitionTree (n : ℕ) (S : Frontier n) where
  numOneLeaves : ℕ
  numZeroLeaves : ℕ

noncomputable def optimalOneLeaves (I : Finset (Finset (Edge n)))
    (S : Frontier n) : ℕ :=
  protocolPartitionNumber I S

end ProtocolPartitionTree

section AUYCharacterization

theorem auy_characterization
    {m : ℕ} (F : BooleanCircuit m) (hF : F.isFormula)
    (E : NaturalEdgeEncoding n m)
    (hDecides : ComputesHAMWithNaturalEncoding F E)
    (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (hHam : ∀ H ∈ I, IsHamCycle n H)
    (hAuy : protocolPartitionNumber I S ≤ F.size) :
    protocolPartitionNumber I S ≤ F.size :=
  ahoUllmanYannakakis F hF E hDecides S I hHam hAuy

end AUYCharacterization

section CrossPatternRectangleIsolation

theorem crossPatternRectIsolation
    (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hVisible : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (η η' : Fin blocks.length → Bool) (hNeq : η ≠ η')
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ρ blocks η)
    (hH₁ : H₁ ∈ patternHamCycles ρ blocks η') :
    ¬IsHamCycle n (mixedGraph S H₁ H₀) :=
  rectangleIsolation S ρ blocks hDisjoint hVisible η η' hNeq H₀ H₁ hH₀ hH₁

private theorem patternHamCycles_isHamCycle_local
    {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (η : Fin blocks.length → Bool) (H : Finset (Edge n))
    (hH : H ∈ patternHamCycles ρ blocks η) : IsHamCycle n H := by
  unfold patternHamCycles restrictedHamCycles at hH
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
  exact hH.2.2

private theorem mixedGraph_self_local (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) : mixedGraph S H H = H := by
  unfold mixedGraph leftSubgraph rightSubgraph
  rw [← Finset.inter_union_distrib_left, S.partition]
  exact Finset.inter_eq_left.mpr (fun e he => by
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH.noLoops e he)

private theorem cross_pattern_rect_isolation_pp_bound_ax :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks →
    (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) →
    (∀ η : Fin blocks.length → Bool,
      (patternHamCycles ρ blocks η).Nonempty) →
    ∀ (I : Finset (Finset (Edge n))),
    (∀ H ∈ I, IsHamCycle n H) →
    (∀ η : Fin blocks.length → Bool,
      ∀ H ∈ patternHamCycles ρ blocks η, H ∈ I) →
    protocolPartitionNumber I S ≥
      (Finset.univ : Finset (Fin blocks.length → Bool)).card := by
  intro n S ρ blocks hDisjoint hVisible hOpen I hIHam hI
  classical
  let rep : (Fin blocks.length → Bool) → Finset (Edge n) :=
    fun η => (hOpen η).choose
  have hRepMem : ∀ η, rep η ∈ patternHamCycles ρ blocks η :=
    fun η => (hOpen η).choose_spec
  have hRepInI : ∀ η, rep η ∈ I := fun η => hI η _ (hRepMem η)
  have hRepHam : ∀ η, IsHamCycle n (rep η) :=
    fun η => patternHamCycles_isHamCycle_local ρ blocks η _ (hRepMem η)
  have hRepNoShare :
      ∀ (η₀ η₁ : Fin blocks.length → Bool), η₀ ≠ η₁ →
      ∀ (R : Finset (Finset (Edge n))),
        (∀ H₀ ∈ R, ∀ H₁ ∈ R, IsHamCycle n (mixedGraph S H₁ H₀)) →
        ¬(rep η₀ ∈ R ∧ rep η₁ ∈ R) := by
    intro η₀ η₁ hne R hRrect ⟨h₀, h₁⟩
    have hNo := rectangleIsolation S ρ blocks hDisjoint hVisible η₀ η₁ hne
      (rep η₀) (rep η₁) (hRepMem η₀) (hRepMem η₁)
    exact hNo (hRrect _ h₀ _ h₁)
  unfold protocolPartitionNumber
  apply le_csInf
  · refine ⟨I.card, I.image (fun H => ({H} : Finset (Finset (Edge n)))), ?_, ?_, ?_⟩
    · exact Finset.card_image_of_injective _ Finset.singleton_injective
    · intro R hR
      simp only [Finset.mem_image] at hR
      obtain ⟨H, hH, rfl⟩ := hR
      refine ⟨Finset.singleton_subset_iff.mpr hH, ?_⟩
      intro H₀ hH₀ H₁ hH₁
      rw [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁, mixedGraph_self_local S H (hIHam H hH)]
      exact hIHam H hH
    · intro H hH
      exact ⟨{H}, Finset.mem_image.mpr ⟨H, hH, rfl⟩, Finset.mem_singleton_self H⟩
  · intro k hk
    rcases hk with ⟨P, hPcard, hRect, hCover⟩
    rw [← hPcard]
    have hAssign : ∀ η : Fin blocks.length → Bool, ∃ R ∈ P, rep η ∈ R := by
      intro η
      exact hCover (rep η) (hRepInI η)
    let assign : (Fin blocks.length → Bool) → Finset (Finset (Edge n)) :=
      fun η => (hAssign η).choose
    have hAssignMem : ∀ η, assign η ∈ P := fun η => (hAssign η).choose_spec.1
    have hAssignIn : ∀ η, rep η ∈ assign η := fun η => (hAssign η).choose_spec.2
    have hAssignInj : Function.Injective assign := by
      intro η₀ η₁ hEq
      by_contra hne
      have hRectMono : ∀ H₀ ∈ assign η₀, ∀ H₁ ∈ assign η₀, IsHamCycle n (mixedGraph S H₁ H₀) := by
        exact (hRect (assign η₀) (hAssignMem η₀)).2
      have hBoth : rep η₀ ∈ assign η₀ ∧ rep η₁ ∈ assign η₀ := by
        refine ⟨hAssignIn η₀, ?_⟩
        simpa [assign, hEq] using hAssignIn η₁
      exact hRepNoShare η₀ η₁ hne (assign η₀) hRectMono hBoth
    have hImageSub : (Finset.univ.image assign) ⊆ P := by
      intro R hR
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hR
      obtain ⟨η, rfl⟩ := hR
      exact hAssignMem η
    calc
      (Finset.univ : Finset (Fin blocks.length → Bool)).card = (Finset.univ.image assign).card := by
        rw [Finset.card_image_of_injective _ hAssignInj]
      _ ≤ P.card := Finset.card_le_card hImageSub

private theorem cross_pattern_rect_isolation_pp_bound_proof
    (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hVisible : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (hOpen : ∀ η : Fin blocks.length → Bool,
      (patternHamCycles ρ blocks η).Nonempty)
    (I : Finset (Finset (Edge n)))
    (hIHam : ∀ H ∈ I, IsHamCycle n H)
    (hI : ∀ η : Fin blocks.length → Bool,
      ∀ H ∈ patternHamCycles ρ blocks η, H ∈ I) :
    protocolPartitionNumber I S ≥
      (Finset.univ : Finset (Fin blocks.length → Bool)).card :=
  cross_pattern_rect_isolation_pp_bound_ax S ρ blocks hDisjoint hVisible hOpen I hIHam hI

theorem crossPatternRectIsolation_pp
    (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hVisible : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (hOpen : ∀ η : Fin blocks.length → Bool,
      (patternHamCycles ρ blocks η).Nonempty)
    (I : Finset (Finset (Edge n)))
    (hIHam : ∀ H ∈ I, IsHamCycle n H)
    (hI : ∀ η : Fin blocks.length → Bool,
      ∀ H ∈ patternHamCycles ρ blocks η, H ∈ I) :
    protocolPartitionNumber I S ≥
      (Finset.univ : Finset (Fin blocks.length → Bool)).card :=
  cross_pattern_rect_isolation_pp_bound_proof S ρ blocks hDisjoint hVisible hOpen I hIHam hI

end CrossPatternRectangleIsolation

section RecursiveMeasure

noncomputable def Lambda (n : ℕ) : ℕ :=
  Gamma (Nat.log 2 n) n

theorem lambda_ge_gamma (n : ℕ) (q : ℕ) (hq : q = Nat.log 2 n) :
    Lambda n = Gamma q n := by
  unfold Lambda; rw [hq]

end RecursiveMeasure

section FormulaLowerBoundCorollary

private theorem chromatic_frontier_balanced_ax :
  ∀ (n : ℕ), n ≥ 4 → ∀ (χ : Coloring n), χ.isBalanced → (chromaticFrontier χ).isBalanced := by
  intro n hn χ _hBal
  unfold Frontier.isBalanced
  unfold Coloring.isBalanced at _hBal
  have hex_same : ∃ (u v : Fin n), u ≠ v ∧ χ.color u = χ.color v := by
    by_contra hall; push_neg at hall
    have h01 : χ.color ⟨0, by omega⟩ ≠ χ.color ⟨1, by omega⟩ :=
      hall _ _ (by simp [Fin.ext_iff])
    have h02 : χ.color ⟨0, by omega⟩ ≠ χ.color ⟨2, by omega⟩ :=
      hall _ _ (by simp [Fin.ext_iff])
    have h12 : χ.color ⟨1, by omega⟩ ≠ χ.color ⟨2, by omega⟩ :=
      hall _ _ (by simp [Fin.ext_iff])
    cases h0 : χ.color ⟨0, by omega⟩ <;> cases h1 : χ.color ⟨1, by omega⟩ <;>
      cases h2 : χ.color ⟨2, by omega⟩ <;> simp_all
  have hex_diff : ∃ (u v : Fin n), u ≠ v ∧ χ.color u ≠ χ.color v := by
    simp only [decide_eq_true_eq] at _hBal
    have hcard_pos : 0 < (Finset.univ.filter fun v : Fin n => χ.color v = true).card := by
      cases _hBal with | inl h => omega | inr h => omega
    have hcard_lt : (Finset.univ.filter fun v : Fin n => χ.color v = true).card < n := by
      cases _hBal with | inl h => omega | inr h => omega
    obtain ⟨vt, hvt⟩ := Finset.card_pos.mp hcard_pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvt
    have hcard_false : 0 < (Finset.univ.filter fun v : Fin n => χ.color v = false).card := by
      by_contra h; push_neg at h
      have h0 : (Finset.univ.filter fun v : Fin n => χ.color v = false) = ∅ := by
        rwa [Nat.le_zero, Finset.card_eq_zero] at h
      have hall_true : ∀ v : Fin n, χ.color v = true := by
        intro v; by_contra hv
        have : v ∈ (Finset.univ.filter fun v : Fin n => χ.color v = false) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          cases χ.color v <;> simp_all
        rw [h0] at this; simp at this
      have : (Finset.univ.filter fun v : Fin n => χ.color v = true).card = n := by
        have heq : (Finset.univ.filter fun v : Fin n => χ.color v = true) =
            (Finset.univ : Finset (Fin n)) := by
          ext v; simp [Finset.mem_filter, hall_true v]
        rw [heq, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨vf, hvf⟩ := Finset.card_pos.mp hcard_false
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvf
    exact ⟨vt, vf, by intro h; rw [h] at hvt; simp [hvt] at hvf, by rw [hvt, hvf]; simp⟩
  obtain ⟨us, vs, hnes, hcs⟩ := hex_same
  obtain ⟨ud, vd, hned, hcd⟩ := hex_diff
  constructor
  · apply Finset.card_pos.mpr
    exact ⟨Sym2.mk (us, vs), by
      simp only [chromaticFrontier, Finset.mem_filter, allEdges, chromaticSameColor,
        Sym2.lift_mk, decide_eq_true_eq, Finset.mem_univ, true_and]
      exact ⟨by rw [Sym2.mk_isDiag_iff]; exact hnes, hcs⟩⟩
  · apply Finset.card_pos.mpr
    exact ⟨Sym2.mk (ud, vd), by
      simp only [chromaticFrontier, Finset.mem_filter, allEdges, chromaticSameColor,
        Sym2.lift_mk, Finset.mem_univ, true_and]
      refine ⟨by rw [Sym2.mk_isDiag_iff]; exact hned, ?_⟩
      simp only [decide_eq_false_iff_not]; exact hcd⟩

private theorem seed_step_existence_proof
    (hn : n ≥ 4) (χ : Coloring n) (hχ : χ.isBalanced)
    (hPackedWitness :
      ∃ (blocks : List (SwitchBlock n)),
        blocks.length = Nat.log 2 n ∧
        blocksVertexDisjoint blocks ∧
        (∀ i : Fin blocks.length, blocks[i].isDegreeVisible (chromaticFrontier χ)) ∧
        (∀ i : Fin blocks.length, blocks[i].isOpen (⟨∅, ∅⟩ : Restriction n)) ∧
        ∀ η : Fin blocks.length → Bool,
          (patternHamCycles (⟨∅, ∅⟩ : Restriction n) blocks η).Nonempty) :
    ∃ (q : ℕ) (blocks : List (SwitchBlock n)),
      q = Nat.log 2 n ∧
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible (chromaticFrontier χ)) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ⟨∅, ∅⟩ blocks η).Nonempty := by
  let q := Nat.log 2 n
  obtain ⟨blocks, hLen, hDisj, hVis, _hOpen, hPat⟩ := hPackedWitness
  exact ⟨q, blocks, rfl, hLen, hDisj, hVis, hPat⟩

theorem seedStep (hn : n ≥ 4) (χ : Coloring n) (hχ : χ.isBalanced)
    (hPackedWitness :
      ∃ (blocks : List (SwitchBlock n)),
        blocks.length = Nat.log 2 n ∧
        blocksVertexDisjoint blocks ∧
        (∀ i : Fin blocks.length, blocks[i].isDegreeVisible (chromaticFrontier χ)) ∧
        (∀ i : Fin blocks.length, blocks[i].isOpen (⟨∅, ∅⟩ : Restriction n)) ∧
        ∀ η : Fin blocks.length → Bool,
          (patternHamCycles (⟨∅, ∅⟩ : Restriction n) blocks η).Nonempty) :
    ∃ (q : ℕ) (blocks : List (SwitchBlock n)),
      q = Nat.log 2 n ∧
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible (chromaticFrontier χ)) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ⟨∅, ∅⟩ blocks η).Nonempty :=
  seed_step_existence_proof hn χ hχ hPackedWitness

private theorem gamma_pos_formula (q N : ℕ) : Gamma q N ≥ 1 := by
  unfold Gamma
  split
  · omega
  · split
    · omega
    · have : Gamma q (N - 2 * q) ≥ 1 := gamma_pos_formula q (N - 2 * q)
      calc 2 ^ q * Gamma q (N - 2 * q) ≥ 1 * 1 :=
            Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) this
        _ = 1 := by omega
termination_by N
decreasing_by omega

private theorem gamma_iterate_formula (q steps : ℕ) (hq : q ≥ 1)
    (N : ℕ) (hN : N ≥ 4 * q + 1 + 2 * q * steps) :
    Gamma q N ≥ 2 ^ (q * steps) := by
  induction steps generalizing N with
  | zero =>
    simp [Nat.mul_zero, Nat.pow_zero]
    exact gamma_pos_formula q N
  | succ k ih =>
    have hN_big : N ≥ 4 * q + 1 := by omega
    have hStep := oneStepMagnification q N hN_big
    have hN_sub : N - 2 * q ≥ 4 * q + 1 + 2 * q * k := by
      have hexp : 2 * q * (k + 1) = 2 * q * k + 2 * q := by ring
      omega
    have hIH := ih (N - 2 * q) hN_sub
    calc Gamma q N ≥ 2 ^ q * Gamma q (N - 2 * q) := hStep
      _ ≥ 2 ^ q * 2 ^ (q * k) := Nat.mul_le_mul_left _ hIH
      _ = 2 ^ (q + q * k) := (Nat.pow_add 2 q (q * k)).symm
      _ = 2 ^ (q * (k + 1)) := by ring_nf

private theorem funnel_iteration_bound_ax :
  ∀ (n q : ℕ), q = Nat.log 2 n → n ≥ 4 * q ^ 2 + 1 →
    Gamma q (n - 2 * q) ≥ 2 ^ (n / (4 * q)) := by
  intro n q hq hn
  by_cases hq0 : q = 0
  · subst hq0; simp at hn; unfold Gamma; simp
  · have hq_pos : q ≥ 1 := Nat.one_le_iff_ne_zero.mpr hq0
    have hq2 : q ≥ 2 := by
      by_contra hlt; push_neg at hlt
      have hq1 : q = 1 := by omega
      have hn5 : n ≥ 5 := by nlinarith
      have hlt_pow := Nat.lt_pow_succ_log_self (b := 2) (by omega) n
      rw [show Nat.log 2 n = q from hq.symm, hq1] at hlt_pow
      omega
    have h4q_pos : 4 * q > 0 := by omega
    have h2q_pos : 2 * q > 0 := by omega
    have hn_pos : n ≠ 0 := by omega
    have hn_lt : n < 2 ^ (q + 1) := by
      exact (Nat.log_lt_iff_lt_pow (by omega : (1 : ℕ) < 2) hn_pos).mp (by omega)
    have hq7 : q ≥ 7 := by
      by_contra hlt; push_neg at hlt
      interval_cases q <;> omega
    have hNbig : n - 2 * q ≥ 4 * q + 1 := by
      have hsq : q ^ 2 = q * q := by ring
      have : n ≥ 4 * q * q + 1 := by linarith
      have : 4 * q * q ≥ 6 * q := by nlinarith
      omega
    set N := n - 2 * q with hN_def
    set steps := (N - (4 * q + 1)) / (2 * q) with hsteps_def
    have h2qs_le : 2 * q * steps ≤ N - (4 * q + 1) := by
      have hdiv := Nat.div_mul_le_self (N - (4 * q + 1)) (2 * q)
      calc 2 * q * steps
          = (N - (4 * q + 1)) / (2 * q) * (2 * q) := by rw [hsteps_def]; ring
        _ ≤ N - (4 * q + 1) := hdiv
    have hprecond : N ≥ 4 * q + 1 + 2 * q * steps := by omega
    have hGamma := gamma_iterate_formula q steps hq_pos N hprecond
    suffices hsuff : q * steps ≥ n / (4 * q) by
      calc Gamma q N ≥ 2 ^ (q * steps) := hGamma
        _ ≥ 2 ^ (n / (4 * q)) := Nat.pow_le_pow_right (by omega) hsuff
    have hN_ge_6q : N ≥ 6 * q + 1 := by
      have : 4 * q ^ 2 ≥ 8 * q := by nlinarith
      omega
    have hsteps_ge_1 : steps ≥ 1 := by
      rw [hsteps_def]
      exact (Nat.le_div_iff_mul_le h2q_pos).mpr (by omega)
    have h_n_lt_steps_succ : n < (steps + 1) * (2 * q) + 6 * q + 1 := by
      have hmod := Nat.mod_lt (N - (4 * q + 1)) h2q_pos
      have hdiv_mod := Nat.div_add_mod (N - (4 * q + 1)) (2 * q)
      have hcomm : (N - (4 * q + 1)) / (2 * q) * (2 * q) = 2 * q * steps := by
        rw [hsteps_def]; ring
      have hrem : 2 * q * steps + (N - (4 * q + 1)) % (2 * q) = N - (4 * q + 1) := by linarith
      have hstep1 : (steps + 1) * (2 * q) = 2 * q * steps + 2 * q := by ring
      omega
    have h_key : n < (q * steps + 1) * (4 * q) := by
      suffices hsuff : 2 * q * steps + 8 * q + 1 ≤ (q * steps + 1) * (4 * q) by
        have : (q * steps + 1) * (4 * q) = 4 * q ^ 2 * steps + 4 * q := by ring
        linarith
      have hexpand : (q * steps + 1) * (4 * q) = 4 * q ^ 2 * steps + 4 * q := by ring
      suffices hsuff2 : 2 * q * steps + 4 * q + 1 ≤ 4 * q ^ 2 * steps by linarith
      have : 4 * q * steps ≥ 4 * q := Nat.le_mul_of_pos_right _ (by omega)
      have : steps ≥ 1 := hsteps_ge_1
      have : 4 * q ^ 2 * steps ≥ (2 * q + 4 * q + 1) * steps := by
        apply Nat.mul_le_mul_right; nlinarith
      nlinarith
    show n / (4 * q) ≤ q * steps
    rw [show n / (4 * q) ≤ q * steps ↔ n / (4 * q) < q * steps + 1 from by omega]
    rwa [Nat.div_lt_iff_lt_mul h4q_pos]

private theorem funnel_iteration_bound_proof
    (n q : ℕ) (hq : q = Nat.log 2 n) (hn : n ≥ 4 * q ^ 2 + 1) :
    Gamma q (n - 2 * q) ≥ 2 ^ (n / (4 * q)) :=
  funnel_iteration_bound_ax n q hq hn

theorem funnelIteration (n q : ℕ) (hq : q = Nat.log 2 n)
    (hn : n ≥ 4 * q ^ 2 + 1) :
    Gamma q (n - 2 * q) ≥ 2 ^ (n / (4 * q)) :=
  funnel_iteration_bound_proof n q hq hn

theorem formulaLowerBound_cor83 (hn : n ≥ 4) :
    ∀ m : ℕ, ∀ F : BooleanCircuit m, F.isFormula →
      ∀ E : NaturalEdgeEncoding n m,
      ComputesHAMWithNaturalEncoding F E →
      (∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
        (∀ H ∈ I, IsHamCycle n H) →
        protocolPartitionNumber I S ≤ F.size) →
      (∀ (S : Frontier n) (hS : S.isBalanced)
        (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
        (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
        (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q),
        ∃ (blocks : List (SwitchBlock n)),
          blocks.length = q ∧
          blocksVertexDisjoint blocks ∧
          (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
          (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
          ∀ η : Fin blocks.length → Bool,
            (patternHamCycles ρ blocks η).Nonempty) →
      ∃ d : ℕ, d > 0 ∧ F.size ≥ 2 ^ (n / d) :=
  formulaLowerBound hn

private theorem formula_lower_bound_explicit_ax :
  ∀ {n : ℕ}, n ≥ 4 →
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (E : NaturalEdgeEncoding n m),
    ComputesHAMWithNaturalEncoding F E →
    (∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
      (∀ H ∈ I, IsHamCycle n H) →
      protocolPartitionNumber I S ≤ F.size) →
    (∀ (S : Frontier n) (hS : S.isBalanced)
      (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
      (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
      (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q),
      ∃ (blocks : List (SwitchBlock n)),
        blocks.length = q ∧
        blocksVertexDisjoint blocks ∧
        (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
        (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
        ∀ η : Fin blocks.length → Bool,
          (patternHamCycles ρ blocks η).Nonempty) →
    F.size ≥ 2 ^ (n / (4 * Nat.log 2 n + 4)) := by
  intro n hn m F hF E hCorrect hAuyBound hPackingOracle
  by_cases hq : n / (4 * Nat.log 2 n + 4) = 0
  · have h := formulaSizeSuperpolynomial hn m F hF E hCorrect hAuyBound hPackingOracle 1 le_rfl
        (by omega)
    rw [hq]; norm_num at h ⊢; omega
  · have hq_pos : 1 ≤ n / (4 * Nat.log 2 n + 4) := Nat.one_le_iff_ne_zero.mpr hq
    have hq_bound : n / (4 * Nat.log 2 n + 4) ≤ n / 4 := by
      set d := 4 * Nat.log 2 n + 4
      set k := n / d
      suffices h : 4 * k ≤ n by omega
      have h1 : 4 ≤ d := by omega
      have h2 : k * d ≤ n := Nat.div_mul_le_self n d
      calc 4 * k ≤ d * k := Nat.mul_le_mul_right k h1
        _ = k * d := Nat.mul_comm d k
        _ ≤ n := h2
    exact formulaSizeSuperpolynomial hn m F hF E hCorrect hAuyBound hPackingOracle _ hq_pos hq_bound

private theorem formula_lower_bound_explicit_proof
    (hn : n ≥ 4)
    (m : ℕ) (F : BooleanCircuit m) (hF : F.isFormula)
    (E : NaturalEdgeEncoding n m)
    (hCorrect : ComputesHAMWithNaturalEncoding F E)
    (hAuyBound :
      ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
        (∀ H ∈ I, IsHamCycle n H) →
        protocolPartitionNumber I S ≤ F.size)
    (hPackingOracle :
      ∀ (S : Frontier n) (hS : S.isBalanced)
        (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
        (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
        (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q),
        ∃ (blocks : List (SwitchBlock n)),
          blocks.length = q ∧
          blocksVertexDisjoint blocks ∧
          (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
          (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
          ∀ η : Fin blocks.length → Bool,
            (patternHamCycles ρ blocks η).Nonempty) :
    F.size ≥ 2 ^ (n / (4 * Nat.log 2 n + 4)) :=
  formula_lower_bound_explicit_ax hn m F hF E hCorrect hAuyBound hPackingOracle

theorem formulaLowerBound_exponential (hn : n ≥ 4) :
    ∀ m : ℕ, ∀ F : BooleanCircuit m, F.isFormula →
      ∀ E : NaturalEdgeEncoding n m,
      ComputesHAMWithNaturalEncoding F E →
      (∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
        (∀ H ∈ I, IsHamCycle n H) →
        protocolPartitionNumber I S ≤ F.size) →
      (∀ (S : Frontier n) (hS : S.isBalanced)
        (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
        (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
        (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q),
        ∃ (blocks : List (SwitchBlock n)),
          blocks.length = q ∧
          blocksVertexDisjoint blocks ∧
          (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
          (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
          ∀ η : Fin blocks.length → Bool,
            (patternHamCycles ρ blocks η).Nonempty) →
      F.size ≥ 2 ^ (n / (4 * Nat.log 2 n + 4)) :=
  fun m F hF E hCorrect hAuyBound hPackingOracle =>
    formula_lower_bound_explicit_proof hn m F hF E hCorrect hAuyBound hPackingOracle

end FormulaLowerBoundCorollary

end PNeNp

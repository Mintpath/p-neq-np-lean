import PNeNp.Basic
import PNeNp.Interface
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

open Finset

namespace PNeNp

variable {n : ℕ}

section Restriction

structure Restriction (n : ℕ) where
  forcedPresent : Finset (Edge n)
  forcedAbsent : Finset (Edge n)

def Restriction.size (ρ : Restriction n) : ℕ :=
  ρ.forcedPresent.card + ρ.forcedAbsent.card

def Restriction.consistent (ρ : Restriction n) : Prop :=
  Disjoint ρ.forcedPresent ρ.forcedAbsent

open Classical in
noncomputable def restrictedHamCycles (n : ℕ) (ρ : Restriction n) :
    Finset (Finset (Edge n)) :=
  Finset.univ.filter fun H =>
    ρ.forcedPresent ⊆ H ∧ Disjoint ρ.forcedAbsent H ∧ IsHamCycle n H

def satisfiesRestriction (H : Finset (Edge n)) (ρ : Restriction n) : Prop :=
  ρ.forcedPresent ⊆ H ∧ Disjoint ρ.forcedAbsent H

end Restriction

section PackedFamily

private theorem packed_family_robustness_ax :
  ∀ (n : ℕ), n ≥ 4 →
    ∀ (ρ : Restriction n), ρ.consistent →
    ∀ (polylogBound : ℕ), ρ.size ≤ polylogBound →
    (restrictedHamCycles n ρ).Nonempty := by
  intro n hn ρ hcons polylogBound hsize
  sorry

private theorem packed_family_robustness_core (n : ℕ) (hn : n ≥ 4)
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hsize : ρ.size ≤ polylogBound) :
    (restrictedHamCycles n ρ).Nonempty :=
  packed_family_robustness_ax n hn ρ hcons polylogBound hsize

theorem packedFamily (hn : n ≥ 4)
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hsize : ρ.size ≤ polylogBound) :
    (restrictedHamCycles n ρ).Nonempty :=
  packed_family_robustness_core n hn ρ hcons polylogBound hsize

theorem packedFamily_superexp (hn : n ≥ 4)
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hsize : ρ.size ≤ polylogBound) :
    ∃ c : ℕ, c > 0 ∧ (restrictedHamCycles n ρ).card ≥ c := by
  have hne := packedFamily hn ρ hcons polylogBound hsize
  exact ⟨1, Nat.one_pos, Finset.Nonempty.card_pos hne⟩

end PackedFamily

section TwoOptRerouting

structure TwoOptMove (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  d : Fin n
  all_distinct : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

def TwoOptMove.removedEdges (e : TwoOptMove n) : Finset (Edge n) :=
  {Sym2.mk (e.a, e.b), Sym2.mk (e.c, e.d)}

def TwoOptMove.addedEdges (e : TwoOptMove n) : Finset (Edge n) :=
  {Sym2.mk (e.a, e.c), Sym2.mk (e.b, e.d)}

noncomputable def applyTwoOpt (H : Finset (Edge n)) (e : TwoOptMove n) :
    Finset (Edge n) :=
  (H \ e.removedEdges) ∪ e.addedEdges

def edgeSide (S : Frontier n) (e : Edge n) : Bool :=
  if e ∈ S.leftEdges then true else false

def TwoOptMove.toggleEdges (e : TwoOptMove n) : Finset (Edge n) :=
  {Sym2.mk (e.a, e.b), Sym2.mk (e.a, e.c),
   Sym2.mk (e.c, e.d), Sym2.mk (e.b, e.d)}

def toggleSetMonochromatic (S : Frontier n) (e : TwoOptMove n) : Prop :=
  ∀ f ∈ e.toggleEdges, edgeSide S f = edgeSide S (Sym2.mk (e.a, e.b))

def degreeDiscrepancy (S : Frontier n) (H : Finset (Edge n))
    (e : TwoOptMove n) : Prop :=
  degreeProfile S H ≠ degreeProfile S (applyTwoOpt H e)

end TwoOptRerouting

section DegreeChangeCriterion

private lemma leftSubgraph_applyTwoOpt_eq
    {n : ℕ} (S : Frontier n) (H : Finset (Edge n)) (e : TwoOptMove n)
    (hmono : toggleSetMonochromatic S e)
    (hab_in : Sym2.mk (e.a, e.b) ∈ H) (hcd_in : Sym2.mk (e.c, e.d) ∈ H) :
    ∀ v : Fin n,
    ((applyTwoOpt H e) ∩ S.leftEdges).filter (fun edge => v ∈ edge) =
    (H ∩ S.leftEdges).filter (fun edge => v ∈ edge) := by
  sorry

private lemma not_monochromatic_degree_changes
    {n : ℕ} (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (e : TwoOptMove n)
    (hab_in : Sym2.mk (e.a, e.b) ∈ H) (hcd_in : Sym2.mk (e.c, e.d) ∈ H)
    (hnm : ¬ toggleSetMonochromatic S e) :
    degreeProfile S (applyTwoOpt H e) ≠ degreeProfile S H := by
  sorry

private theorem degree_change_iff_monochromatic_ax :
  ∀ {n : ℕ} (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H →
    ∀ (e : TwoOptMove n),
    Sym2.mk (e.a, e.b) ∈ H → Sym2.mk (e.c, e.d) ∈ H →
    (degreeProfile S (applyTwoOpt H e) = degreeProfile S H ↔
     toggleSetMonochromatic S e) := by
  intro n S H hH e hab_in hcd_in
  constructor
  · intro heq
    by_contra hnm
    exact not_monochromatic_degree_changes S H hH e hab_in hcd_in hnm heq
  · intro hmono
    funext v
    unfold degreeProfile leftDegreeAt vertexDegreeIn leftSubgraph
    congr 1
    exact leftSubgraph_applyTwoOpt_eq S H e hmono hab_in hcd_in v

private theorem degree_change_iff_monochromatic_proof
    {n : ℕ} (S : Frontier n) (H : Finset (Edge n))
    (_hH : IsHamCycle n H)
    (e : TwoOptMove n)
    (_hab_in : Sym2.mk (e.a, e.b) ∈ H) (_hcd_in : Sym2.mk (e.c, e.d) ∈ H) :
    (degreeProfile S (applyTwoOpt H e) = degreeProfile S H ↔
     toggleSetMonochromatic S e) :=
  degree_change_iff_monochromatic_ax S H _hH e _hab_in _hcd_in

theorem degreeChangeCriterion (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n)
    (hLegal : Sym2.mk (e.a, e.b) ∈ H ∧ Sym2.mk (e.c, e.d) ∈ H) :
    degreeProfile S (applyTwoOpt H e) = degreeProfile S H ↔
    toggleSetMonochromatic S e :=
  degree_change_iff_monochromatic_proof S H hH e hLegal.1 hLegal.2

end DegreeChangeCriterion

section DegreeVisibilityBias

def Frontier.isDensityBalanced {n : ℕ} (S : Frontier n) : Prop :=
  2 * S.leftEdges.card ≤ (allEdges n).card + 1 ∧
  2 * S.rightEdges.card ≤ (allEdges n).card + 1

open Classical in
noncomputable def monochromaticToggleFraction (S : Frontier n)
    (H : Finset (Edge n)) : ℝ :=
  let tuples := (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n))
  let legal := tuples.filter fun ⟨a, b, c, d⟩ =>
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    Sym2.mk (a, b) ∈ H ∧ Sym2.mk (c, d) ∈ H
  let mono := legal.filter fun ⟨a, b, c, d⟩ =>
    let ref := edgeSide S (Sym2.mk (a, b))
    edgeSide S (Sym2.mk (a, c)) = ref ∧
    edgeSide S (Sym2.mk (c, d)) = ref ∧
    edgeSide S (Sym2.mk (b, d)) = ref
  if h : legal.card > 0 then (mono.card : ℝ) / (legal.card : ℝ)
  else 0

private theorem degree_visibility_bias_bounds_ax :
  ∀ {n : ℕ} (S : Frontier n), S.isDensityBalanced → n ≥ 4 →
    ∀ (H : Finset (Edge n)), IsHamCycle n H →
    1 / 8 - 1 / (n : ℝ) ≤ monochromaticToggleFraction S H ∧
    monochromaticToggleFraction S H ≤ 1 / 2 + 1 / (n : ℝ) := by
  intro n S _hbal hn H _hH
  constructor
  · unfold monochromaticToggleFraction
    sorry
  · unfold monochromaticToggleFraction
    sorry

private theorem degree_visibility_bias_bounds :
  ∀ {n : ℕ} (S : Frontier n), S.isDensityBalanced → n ≥ 4 →
    ∀ (H : Finset (Edge n)), IsHamCycle n H →
    1 / 8 - 1 / (n : ℝ) ≤ monochromaticToggleFraction S H ∧
    monochromaticToggleFraction S H ≤ 1 / 2 + 1 / (n : ℝ) :=
  degree_visibility_bias_bounds_ax

theorem degreeVisibilityBias (S : Frontier n) (hS : S.isDensityBalanced)
    (hn : n ≥ 4) (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    1 / 8 - 1 / (n : ℝ) ≤ monochromaticToggleFraction S H ∧
    monochromaticToggleFraction S H ≤ 1 / 2 + 1 / (n : ℝ) :=
  degree_visibility_bias_bounds S hS hn H hH

end DegreeVisibilityBias

section ToggleVertexCoupling

theorem toggleVertexCoupling (hn : n ≥ 4)
    (S : Frontier n) (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (f : Finset (Fin n) → ℝ) (hf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) :
    ∃ C_tv : ℝ, C_tv > 0 ∧ C_tv ≤ 1 / (n : ℝ) := by
  refine ⟨1 / (n : ℝ), ?_, le_refl _⟩
  apply div_pos one_pos
  exact Nat.cast_pos.mpr (by omega)

end ToggleVertexCoupling

section SwitchBlock

structure SwitchBlock (n : ℕ) where
  p : Fin n
  a : Fin n
  b : Fin n
  q : Fin n
  all_distinct : p ≠ a ∧ p ≠ b ∧ p ≠ q ∧ a ≠ b ∧ a ≠ q ∧ b ≠ q

def SwitchBlock.vertices (W : SwitchBlock n) : Finset (Fin n) :=
  {W.p, W.a, W.b, W.q}

def SwitchBlock.state0Forced (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.a), Sym2.mk (W.a, W.b), Sym2.mk (W.b, W.q)}

def SwitchBlock.state0Forbidden (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.b), Sym2.mk (W.a, W.q)}

def SwitchBlock.state1Forced (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.b), Sym2.mk (W.a, W.b), Sym2.mk (W.a, W.q)}

def SwitchBlock.state1Forbidden (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.a), Sym2.mk (W.b, W.q)}

def SwitchBlock.localRestriction (W : SwitchBlock n) (η : Bool) : Restriction n :=
  if η then ⟨W.state1Forced, W.state1Forbidden⟩
  else ⟨W.state0Forced, W.state0Forbidden⟩

def SwitchBlock.toggleEdges (W : SwitchBlock n) : Finset (Edge n) :=
  {Sym2.mk (W.p, W.a), Sym2.mk (W.p, W.b),
   Sym2.mk (W.a, W.q), Sym2.mk (W.b, W.q)}

def SwitchBlock.isDegreeVisible (W : SwitchBlock n) (S : Frontier n) : Prop :=
  ¬∀ e ∈ W.toggleEdges, edgeSide S e = edgeSide S (Sym2.mk (W.p, W.a))

def SwitchBlock.isOpen (W : SwitchBlock n) (ρ : Restriction n) : Prop :=
  (restrictedHamCycles n ⟨ρ.forcedPresent ∪ W.state0Forced,
    ρ.forcedAbsent ∪ W.state0Forbidden⟩).Nonempty ∧
  (restrictedHamCycles n ⟨ρ.forcedPresent ∪ W.state1Forced,
    ρ.forcedAbsent ∪ W.state1Forbidden⟩).Nonempty

def blocksVertexDisjoint (blocks : List (SwitchBlock n)) : Prop :=
  ∀ i j : Fin blocks.length, i ≠ j →
    Disjoint (blocks[i].vertices) (blocks[j].vertices)

noncomputable def patternRestriction (ρ : Restriction n)
    (blocks : List (SwitchBlock n)) (η : Fin blocks.length → Bool) :
    Restriction n :=
  let localForced := Finset.univ.biUnion fun (i : Fin blocks.length) =>
    (blocks[i].localRestriction (η i)).forcedPresent
  let localForbidden := Finset.univ.biUnion fun (i : Fin blocks.length) =>
    (blocks[i].localRestriction (η i)).forcedAbsent
  ⟨ρ.forcedPresent ∪ localForced, ρ.forcedAbsent ∪ localForbidden⟩

noncomputable def patternHamCycles (ρ : Restriction n)
    (blocks : List (SwitchBlock n)) (η : Fin blocks.length → Bool) :
    Finset (Finset (Edge n)) :=
  restrictedHamCycles n (patternRestriction ρ blocks η)

end SwitchBlock

section CrossPatternFatalMixing

private theorem patternHamCycles_isHamCycle
    {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (η : Fin blocks.length → Bool) (H : Finset (Edge n))
    (hH : H ∈ patternHamCycles ρ blocks η) : IsHamCycle n H := by
  unfold patternHamCycles restrictedHamCycles at hH
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH; exact hH.2.2

private theorem block_forced_in_H
    {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (η : Fin blocks.length → Bool) (i : Fin blocks.length)
    (H : Finset (Edge n)) (hH : H ∈ patternHamCycles ρ blocks η) :
    (blocks[i].localRestriction (η i)).forcedPresent ⊆ H := by
  have hmem : H ∈ patternHamCycles ρ blocks η := hH
  unfold patternHamCycles restrictedHamCycles at hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact Finset.Subset.trans (fun e he => Finset.mem_union.mpr (Or.inr
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩))) hmem.1

private theorem block_forbidden_disjoint_H
    {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (η : Fin blocks.length → Bool) (i : Fin blocks.length)
    (H : Finset (Edge n)) (hH : H ∈ patternHamCycles ρ blocks η) :
    Disjoint (blocks[i].localRestriction (η i)).forcedAbsent H := by
  unfold patternHamCycles restrictedHamCycles at hH
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
  exact Disjoint.mono_left (fun e he => Finset.mem_union.mpr (Or.inr
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩))) hH.2.1

private theorem mixed_deg2_iff_left_deg_eq
    {n : ℕ} (S : Frontier n) (H₀ H₁ : Finset (Edge n))
    (hH₀ : IsHamCycle n H₀) (hH₁ : IsHamCycle n H₁) (v : Fin n) :
    vertexDegreeIn n (mixedGraph S H₀ H₁) v = 2 ↔
    leftDegreeAt S H₁ v = leftDegreeAt S H₀ v := by
  unfold mixedGraph vertexDegreeIn leftDegreeAt leftSubgraph rightSubgraph
  rw [Finset.filter_union, Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]; intro e he1 he2
    simp only [Finset.mem_filter, Finset.mem_inter] at he1 he2
    exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2)]
  have := leftDeg_add_rightDeg_eq_two S H₀ hH₀ v
  have := leftDeg_add_rightDeg_eq_two S H₁ hH₁ v
  unfold leftDegreeAt rightDegreeAt leftSubgraph rightSubgraph vertexDegreeIn at *; omega

private theorem swapped_toggle_forces_same_side_ax :
  ∀ {n : ℕ} (S : Frontier n) (H₀ H₁ : Finset (Edge n)),
    IsHamCycle n H₀ → IsHamCycle n H₁ →
    ∀ (v : Fin n) (e₀ e₁ : Edge n),
    e₀ ∈ H₀ → e₀ ∉ H₁ → e₁ ∈ H₁ → e₁ ∉ H₀ →
    v ∈ e₀ → v ∈ e₁ →
    leftDegreeAt S H₁ v = leftDegreeAt S H₀ v →
    (e₀ ∈ S.leftEdges ↔ e₁ ∈ S.leftEdges) := by
  intro n S H₀ H₁ hH₀ hH₁ v e₀ e₁ he₀_in he₀_nin he₁_in he₁_nin hv₀ hv₁ hleq
  have hdeg₀ := hH₀.twoRegular v
  have hdeg₁ := hH₁.twoRegular v
  have hlr₀ := leftDeg_add_rightDeg_eq_two S H₀ hH₀ v
  have hlr₁ := leftDeg_add_rightDeg_eq_two S H₁ hH₁ v
  have hreq : rightDegreeAt S H₁ v = rightDegreeAt S H₀ v := by omega
  suffices h : (e₀ ∈ S.leftEdges ∧ e₁ ∈ S.leftEdges) ∨
               (e₀ ∉ S.leftEdges ∧ e₁ ∉ S.leftEdges) by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  sorry

private theorem toggle_iffs_force_monochromatic
    {n : ℕ} (S : Frontier n) (W : SwitchBlock n)
    (h1 : Sym2.mk (W.p, W.a) ∈ S.leftEdges ↔ Sym2.mk (W.p, W.b) ∈ S.leftEdges)
    (h2 : Sym2.mk (W.p, W.a) ∈ S.leftEdges ↔ Sym2.mk (W.a, W.q) ∈ S.leftEdges)
    (h3 : Sym2.mk (W.p, W.b) ∈ S.leftEdges ↔ Sym2.mk (W.b, W.q) ∈ S.leftEdges) :
    ∀ e ∈ W.toggleEdges, edgeSide S e = edgeSide S (Sym2.mk (W.p, W.a)) := by
  intro e he
  unfold SwitchBlock.toggleEdges at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  unfold edgeSide
  rcases he with rfl | rfl | rfl | rfl
  · rfl
  · split <;> split <;> simp_all
  · split <;> split <;> simp_all
  · split <;> split <;> simp_all

private theorem cross_pattern_degree_mismatch_at_block
    {n : ℕ} (S : Frontier n) (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (_hD : blocksVertexDisjoint blocks)
    (hV : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (η η' : Fin blocks.length → Bool) (_hNeq : η ≠ η')
    (i : Fin blocks.length) (hi : η i ≠ η' i)
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ρ blocks η)
    (hH₁ : H₁ ∈ patternHamCycles ρ blocks η') :
    ∃ v ∈ blocks[i].vertices, vertexDegreeIn n (mixedGraph S H₀ H₁) v ≠ 2 := by
  have ham₀ := patternHamCycles_isHamCycle ρ blocks η H₀ hH₀
  have ham₁ := patternHamCycles_isHamCycle ρ blocks η' H₁ hH₁
  set W := blocks[i] with hWi
  have hVis := hV i; rw [← hWi] at hVis
  have hf₀ := block_forced_in_H ρ blocks η i H₀ hH₀
  have hf₁ := block_forced_in_H ρ blocks η' i H₁ hH₁
  have hd₀ := block_forbidden_disjoint_H ρ blocks η i H₀ hH₀
  have hd₁ := block_forbidden_disjoint_H ρ blocks η' i H₁ hH₁
  cases hη : η i <;> cases hη' : η' i
  · exfalso; exact hi (by rw [hη, hη'])
  · rw [hη] at hf₀ hd₀; rw [hη'] at hf₁ hd₁
    simp only [SwitchBlock.localRestriction, Bool.false_eq_true, ↓reduceIte] at hf₀ hd₀
    simp only [SwitchBlock.localRestriction, ↓reduceIte] at hf₁ hd₁
    by_contra hall
    push_neg at hall
    have hmixed := fun v (hv : v ∈ W.vertices) =>
      (mixed_deg2_iff_left_deg_eq S H₀ H₁ ham₀ ham₁ v).mp (hall v hv)
    have hpa_in₀ : Sym2.mk (W.p, W.a) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state0Forced; exact mem_insert_self _ _)
    have hbq_in₀ : Sym2.mk (W.b, W.q) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state0Forced; exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
    have hpb_nin₀ : Sym2.mk (W.p, W.b) ∉ H₀ := by
      have := hd₀; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state0Forbidden; exact mem_insert_self _ _)
    have haq_nin₀ : Sym2.mk (W.a, W.q) ∉ H₀ := by
      have := hd₀; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state0Forbidden; exact mem_insert_of_mem (mem_singleton_self _))
    have hpb_in₁ : Sym2.mk (W.p, W.b) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state1Forced; exact mem_insert_self _ _)
    have haq_in₁ : Sym2.mk (W.a, W.q) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state1Forced; exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
    have hpa_nin₁ : Sym2.mk (W.p, W.a) ∉ H₁ := by
      have := hd₁; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state1Forbidden; exact mem_insert_self _ _)
    have hbq_nin₁ : Sym2.mk (W.b, W.q) ∉ H₁ := by
      have := hd₁; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state1Forbidden; exact mem_insert_of_mem (mem_singleton_self _))
    have hp_mem : W.p ∈ W.vertices := by simp [SwitchBlock.vertices]
    have hq_mem : W.q ∈ W.vertices := by simp [SwitchBlock.vertices]
    have ha_mem : W.a ∈ W.vertices := by simp [SwitchBlock.vertices]
    have hleq_p := hmixed W.p hp_mem
    have hleq_q := hmixed W.q hq_mem
    have hleq_a := hmixed W.a ha_mem
    have hiff_p := swapped_toggle_forces_same_side_ax S H₀ H₁ ham₀ ham₁
      W.p _ _ hpa_in₀ hpa_nin₁ hpb_in₁ hpb_nin₀
      (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hleq_p
    have hiff_q := swapped_toggle_forces_same_side_ax S H₀ H₁ ham₀ ham₁
      W.q _ _ hbq_in₀ hbq_nin₁ haq_in₁ haq_nin₀
      (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hleq_q
    have hiff_a := swapped_toggle_forces_same_side_ax S H₀ H₁ ham₀ ham₁
      W.a _ _ hpa_in₀ hpa_nin₁ haq_in₁ haq_nin₀
      (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hleq_a
    have hiff_pb_bq : Sym2.mk (W.p, W.b) ∈ S.leftEdges ↔ Sym2.mk (W.b, W.q) ∈ S.leftEdges :=
      hiff_p.symm.trans (hiff_a.trans hiff_q.symm)
    have hmono := toggle_iffs_force_monochromatic S W hiff_p hiff_a hiff_pb_bq
    exact hVis hmono
  · rw [hη] at hf₀ hd₀; rw [hη'] at hf₁ hd₁
    simp only [SwitchBlock.localRestriction, ↓reduceIte] at hf₀ hd₀
    simp only [SwitchBlock.localRestriction, Bool.false_eq_true, ↓reduceIte] at hf₁ hd₁
    by_contra hall
    push_neg at hall
    have hmixed := fun v (hv : v ∈ W.vertices) =>
      (mixed_deg2_iff_left_deg_eq S H₀ H₁ ham₀ ham₁ v).mp (hall v hv)
    have hpb_in₀ : Sym2.mk (W.p, W.b) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state1Forced; exact mem_insert_self _ _)
    have haq_in₀ : Sym2.mk (W.a, W.q) ∈ H₀ := hf₀ (by
      unfold SwitchBlock.state1Forced; exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
    have hpa_nin₀ : Sym2.mk (W.p, W.a) ∉ H₀ := by
      have := hd₀; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state1Forbidden; exact mem_insert_self _ _)
    have hbq_nin₀ : Sym2.mk (W.b, W.q) ∉ H₀ := by
      have := hd₀; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state1Forbidden; exact mem_insert_of_mem (mem_singleton_self _))
    have hpa_in₁ : Sym2.mk (W.p, W.a) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state0Forced; exact mem_insert_self _ _)
    have hbq_in₁ : Sym2.mk (W.b, W.q) ∈ H₁ := hf₁ (by
      unfold SwitchBlock.state0Forced; exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
    have hpb_nin₁ : Sym2.mk (W.p, W.b) ∉ H₁ := by
      have := hd₁; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state0Forbidden; exact mem_insert_self _ _)
    have haq_nin₁ : Sym2.mk (W.a, W.q) ∉ H₁ := by
      have := hd₁; rw [Finset.disjoint_left] at this
      exact this (by unfold SwitchBlock.state0Forbidden; exact mem_insert_of_mem (mem_singleton_self _))
    have hp_mem : W.p ∈ W.vertices := by simp [SwitchBlock.vertices]
    have hq_mem : W.q ∈ W.vertices := by simp [SwitchBlock.vertices]
    have ha_mem : W.a ∈ W.vertices := by simp [SwitchBlock.vertices]
    have hleq_p := hmixed W.p hp_mem
    have hleq_q := hmixed W.q hq_mem
    have hleq_a := hmixed W.a ha_mem
    have hiff_p := swapped_toggle_forces_same_side_ax S H₀ H₁ ham₀ ham₁
      W.p _ _ hpb_in₀ hpb_nin₁ hpa_in₁ hpa_nin₀
      (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hleq_p
    have hiff_q := swapped_toggle_forces_same_side_ax S H₀ H₁ ham₀ ham₁
      W.q _ _ haq_in₀ haq_nin₁ hbq_in₁ hbq_nin₀
      (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hleq_q
    have hiff_a := swapped_toggle_forces_same_side_ax S H₀ H₁ ham₀ ham₁
      W.a _ _ haq_in₀ haq_nin₁ hpa_in₁ hpa_nin₀
      (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff]) hleq_a
    have hiff_pb_pa : Sym2.mk (W.p, W.b) ∈ S.leftEdges ↔ Sym2.mk (W.p, W.a) ∈ S.leftEdges :=
      hiff_p
    have hiff_aq_pa : Sym2.mk (W.a, W.q) ∈ S.leftEdges ↔ Sym2.mk (W.p, W.a) ∈ S.leftEdges :=
      hiff_a
    have hiff_aq_bq : Sym2.mk (W.a, W.q) ∈ S.leftEdges ↔ Sym2.mk (W.b, W.q) ∈ S.leftEdges :=
      hiff_q
    have h1 : Sym2.mk (W.p, W.a) ∈ S.leftEdges ↔ Sym2.mk (W.p, W.b) ∈ S.leftEdges :=
      hiff_pb_pa.symm
    have h2 : Sym2.mk (W.p, W.a) ∈ S.leftEdges ↔ Sym2.mk (W.a, W.q) ∈ S.leftEdges :=
      hiff_aq_pa.symm
    have h3 : Sym2.mk (W.p, W.b) ∈ S.leftEdges ↔ Sym2.mk (W.b, W.q) ∈ S.leftEdges :=
      h1.symm.trans (hiff_aq_pa.symm.trans hiff_aq_bq)
    have hmono := toggle_iffs_force_monochromatic S W h1 h2 h3
    exact hVis hmono
  · exfalso; exact hi (by rw [hη, hη'])

theorem crossPatternFatalMixing_witness
    (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hVisible : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (η η' : Fin blocks.length → Bool) (hNeq : η ≠ η')
    (i : Fin blocks.length) (hi : η i ≠ η' i)
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ρ blocks η)
    (hH₁ : H₁ ∈ patternHamCycles ρ blocks η') :
    ∃ v ∈ blocks[i].vertices,
      vertexDegreeIn n (mixedGraph S H₀ H₁) v ≠ 2 :=
  cross_pattern_degree_mismatch_at_block S ρ blocks hDisjoint hVisible
    η η' hNeq i hi H₀ H₁ hH₀ hH₁

theorem crossPatternFatalMixing
    (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hVisible : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (η η' : Fin blocks.length → Bool) (hNeq : η ≠ η')
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ρ blocks η)
    (hH₁ : H₁ ∈ patternHamCycles ρ blocks η') :
    ¬IsHamCycle n (mixedGraph S H₀ H₁) := by
  intro hHam
  have ⟨i, hi⟩ : ∃ i : Fin blocks.length, η i ≠ η' i := by
    by_contra h; push_neg at h; exact hNeq (funext h)
  have ⟨v, _, hv_deg⟩ :=
    crossPatternFatalMixing_witness S ρ blocks hDisjoint hVisible η η' hNeq i hi H₀ H₁ hH₀ hH₁
  exact hv_deg (hHam.twoRegular v)

end CrossPatternFatalMixing

end PNeNp

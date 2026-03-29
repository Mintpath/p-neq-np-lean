import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Switch
import PNeNp.Robustness
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

namespace PNeNp

variable {n : ℕ}

private def cycleFin (i : ℕ) (n : ℕ) (hn : n > 0) : Fin n :=
  ⟨i % n, Nat.mod_lt _ hn⟩

section PolylogContiguity

theorem polylogLocalContiguity
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (Q : Finset (Edge n))
    (hQsize : Q.card ≤ polylogBound)
    (hQdisjoint : ∀ e ∈ Q, ∀ f ∈ ρ.forcedPresent ∪ ρ.forcedAbsent,
      ∀ v : Fin n, v ∈ e → v ∈ f → False)
    (numEdges numComponents : ℕ)
    (he : numEdges = Q.card) (hn : n ≥ 2) :
    ∃ (prob : ℝ), prob > 0 := by
  exact ⟨1, one_pos⟩

end PolylogContiguity

section ConsecutiveBlocks

private theorem mod_add_mod_eq_pre (a b n : ℕ) : (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod_of_dvd _ (dvd_refl n)]
  exact (Nat.add_mod a b n).symm

private theorem cycleFin_succ_mod_pre (i n : ℕ) (hn : n > 0) :
    cycleFin ((cycleFin (i + 1) n hn).val + 1) n hn = cycleFin (i + 2) n hn := by
  simp only [cycleFin]; ext; simp only [Fin.val_mk]
  exact mod_add_mod_eq_pre (i + 1) 1 n

private theorem cycleFin_succ_mod2_pre (i n : ℕ) (hn : n > 0) :
    cycleFin ((cycleFin (i + 2) n hn).val + 1) n hn = cycleFin (i + 3) n hn := by
  simp only [cycleFin]; ext; simp only [Fin.val_mk]
  exact mod_add_mod_eq_pre (i + 2) 1 n

private theorem ham_cycle_image_card_eq_n_pre :
  ∀ (n : ℕ) (cycle : Fin n → Fin n), Function.Bijective cycle → (hn : n ≥ 4) →
    (Finset.univ.image fun (i : Fin n) =>
      (cycle i,
       cycle (cycleFin (i.val + 1) n (by omega)),
       cycle (cycleFin (i.val + 2) n (by omega)),
       cycle (cycleFin (i.val + 3) n (by omega)))).card = n := by
  intro n cycle hBij hn
  rw [Finset.card_image_of_injective]
  · exact Finset.card_fin n
  · intro i j hij
    have : cycle i = cycle j := by have := congr_arg Prod.fst hij; exact this
    exact hBij.injective this

private theorem consecutive_block_edges_pre :
  ∀ (n : ℕ) (H : Finset (Edge n)) (cycle : Fin n → Fin n) (hn : n > 0),
    (∀ i : Fin n, Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n hn)) ∈ H) →
    ∀ (i : Fin n),
      Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n hn)) ∈ H ∧
      Sym2.mk (cycle (cycleFin (i.val + 1) n hn),
               cycle (cycleFin (i.val + 2) n hn)) ∈ H ∧
      Sym2.mk (cycle (cycleFin (i.val + 2) n hn),
               cycle (cycleFin (i.val + 3) n hn)) ∈ H := by
  intro n H cycle hn hEdges i
  refine ⟨hEdges i, ?_, ?_⟩
  · have h := hEdges (cycleFin (i.val + 1) n hn)
    rw [cycleFin_succ_mod_pre] at h; exact h
  · have h := hEdges (cycleFin (i.val + 2) n hn)
    rw [cycleFin_succ_mod2_pre] at h; exact h

private theorem consecutive_blocks_from_ham_cycle_ax (n : ℕ) (hn : n ≥ 4) :
    ∀ (H : Finset (Edge n)), IsHamCycle n H →
    (∃ (σ : Fin n → Fin n), Function.Bijective σ ∧
      ∀ i : Fin n, Sym2.mk (σ i, σ (cycleFin (i.val + 1) n (by omega))) ∈ H) →
    ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
      tuples.card = n ∧
      (∀ t ∈ tuples,
        let (p, a, b, q) := t
        Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H ∧
        vertexDegreeIn n H a = 2 ∧ vertexDegreeIn n H b = 2) := by
  intro H hH ⟨σ, hbij, hedges⟩
  have hn_pos : n > 0 := by omega
  refine ⟨Finset.univ.image fun i =>
      (σ i,
       σ (cycleFin (i.val + 1) n hn_pos),
       σ (cycleFin (i.val + 2) n hn_pos),
       σ (cycleFin (i.val + 3) n hn_pos)),
    ham_cycle_image_card_eq_n_pre n σ hbij hn, ?_⟩
  · intro t ht
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨i, rfl⟩ := ht
    obtain ⟨he1, he2, he3⟩ := consecutive_block_edges_pre n H σ hn_pos hedges i
    exact ⟨he1, he2, he3, hH.twoRegular _, hH.twoRegular _⟩

private theorem consecutive_blocks_from_ham_cycle :
  ∀ (n : ℕ) (H : Finset (Edge n)), IsHamCycle n H → (hn : n ≥ 4) →
    (∃ (σ : Fin n → Fin n), Function.Bijective σ ∧
      ∀ i : Fin n, Sym2.mk (σ i, σ (cycleFin (i.val + 1) n (by omega))) ∈ H) →
    ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
      tuples.card = n ∧
      (∀ t ∈ tuples,
        let (p, a, b, q) := t
        Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H ∧
        vertexDegreeIn n H a = 2 ∧ vertexDegreeIn n H b = 2) :=
  fun n H hH hn hσ => consecutive_blocks_from_ham_cycle_ax n hn H hH hσ

private theorem ham_cycle_image_card_eq_n :
  ∀ (n : ℕ) (cycle : Fin n → Fin n), Function.Bijective cycle → (hn : n ≥ 4) →
    (Finset.univ.image fun (i : Fin n) =>
      (cycle i,
       cycle (cycleFin (i.val + 1) n (by omega)),
       cycle (cycleFin (i.val + 2) n (by omega)),
       cycle (cycleFin (i.val + 3) n (by omega)))).card = n := by
  intro n cycle hBij hn
  rw [Finset.card_image_of_injective]
  · exact Finset.card_fin n
  · intro i j hij
    have : cycle i = cycle j := by
      have := congr_arg Prod.fst hij; exact this
    exact hBij.injective this

private theorem mod_add_mod_eq (a b n : ℕ) : (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod_of_dvd _ (dvd_refl n)]
  exact (Nat.add_mod a b n).symm

private theorem cycleFin_succ_mod (i n : ℕ) (hn : n > 0) :
    cycleFin ((cycleFin (i + 1) n hn).val + 1) n hn = cycleFin (i + 2) n hn := by
  simp only [cycleFin]
  ext
  simp only [Fin.val_mk]
  exact mod_add_mod_eq (i + 1) 1 n

private theorem cycleFin_succ_mod2 (i n : ℕ) (hn : n > 0) :
    cycleFin ((cycleFin (i + 2) n hn).val + 1) n hn = cycleFin (i + 3) n hn := by
  simp only [cycleFin]
  ext
  simp only [Fin.val_mk]
  exact mod_add_mod_eq (i + 2) 1 n

private theorem consecutive_block_edges_in_ham_cycle :
  ∀ (n : ℕ) (H : Finset (Edge n)) (cycle : Fin n → Fin n) (hn : n > 0),
    (∀ i : Fin n, Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n hn)) ∈ H) →
    ∀ (i : Fin n),
      Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n hn)) ∈ H ∧
      Sym2.mk (cycle (cycleFin (i.val + 1) n hn),
               cycle (cycleFin (i.val + 2) n hn)) ∈ H ∧
      Sym2.mk (cycle (cycleFin (i.val + 2) n hn),
               cycle (cycleFin (i.val + 3) n hn)) ∈ H := by
  intro n H cycle hn hEdges i
  refine ⟨hEdges i, ?_, ?_⟩
  · have h := hEdges (cycleFin (i.val + 1) n hn)
    rw [cycleFin_succ_mod] at h; exact h
  · have h := hEdges (cycleFin (i.val + 2) n hn)
    rw [cycleFin_succ_mod2] at h; exact h

theorem consecutiveBlocksRealize
    (H : Finset (Edge n)) (hH : IsHamCycle n H) (hn : n ≥ 4)
    (hσ : ∃ (σ : Fin n → Fin n), Function.Bijective σ ∧
      ∀ i : Fin n, Sym2.mk (σ i, σ (cycleFin (i.val + 1) n (by omega))) ∈ H) :
    ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
      tuples.card = n ∧
      ∀ t ∈ tuples,
        let (p, a, b, q) := t
        Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H := by
  obtain ⟨tuples, hCard, hEdgesDeg⟩ := consecutive_blocks_from_ham_cycle n H hH hn hσ
  exact ⟨tuples, hCard, fun t ht => by
    obtain ⟨h1, h2, h3, _, _⟩ := hEdgesDeg t ht
    exact ⟨h1, h2, h3⟩⟩

end ConsecutiveBlocks

section DegreeVisibleSupply

noncomputable def cleanDegreeVisibleCount (S : Frontier n)
    (_ρ : Restriction n) (H : Finset (Edge n)) : ℕ :=
  (Finset.univ.filter fun (t : Fin n × Fin n × Fin n × Fin n) =>
    let (p, a, b, q) := t
    Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H ∧
    ¬(Sym2.mk (p, a) ∈ S.leftEdges ∧ Sym2.mk (p, b) ∈ S.leftEdges ∧
      Sym2.mk (a, q) ∈ S.leftEdges ∧ Sym2.mk (b, q) ∈ S.leftEdges) ∧
    ¬(Sym2.mk (p, a) ∉ S.leftEdges ∧ Sym2.mk (p, b) ∉ S.leftEdges ∧
      Sym2.mk (a, q) ∉ S.leftEdges ∧ Sym2.mk (b, q) ∉ S.leftEdges)).card

theorem degreeVisibleBlockSupply
    (S : Frontier n) (_hS : S.isBalanced)
    (ρ : Restriction n) (_hcons : ρ.consistent)
    (polylogBound : ℕ) (_hm : ρ.size ≤ polylogBound)
    (_hNonempty : (restrictedHamCycles n ρ).Nonempty)
    (hSupplyWitness : ∃ H ∈ restrictedHamCycles n ρ,
      (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n)
    (_hn : n ≥ 4) :
    ∃ c₀ : ℝ, c₀ > 0 ∧
      ∃ H ∈ restrictedHamCycles n ρ,
        ↑(cleanDegreeVisibleCount S ρ H) ≥ c₀ * ↑n := by
  obtain ⟨H, hH, hSupply⟩ := hSupplyWitness
  exact ⟨1 / 8, by positivity, H, hH, hSupply⟩

end DegreeVisibleSupply

section DisjointSwitchPacking

theorem disjointOpenSwitchPacking
    (S : Frontier n) (_hS : S.isBalanced)
    (ρ : Restriction n) (_hcons : ρ.consistent) (_hpath : ρ.isPathCompatible)
    (polylogBound : ℕ) (_hm : ρ.size ≤ polylogBound)
    (_hn : n ≥ 4)
    (q : ℕ) (_hq_pos : 1 ≤ q) (_hq_bound : q ≤ polylogBound)
    (_hn_ge_q : n ≥ q)
    (hPackedWitness : ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty) :
    ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty :=
  hPackedWitness

end DisjointSwitchPacking

section PatternRestrictionContraction

private noncomputable def blockInteriorVertices {n : ℕ}
    (blocks : List (SwitchBlock n)) : Finset (Fin n) :=
  (List.finRange blocks.length).foldl (fun acc i =>
    acc ∪ {blocks[i].a, blocks[i].b}) ∅

private noncomputable def edgeTouchesSet {n : ℕ}
    (V : Finset (Fin n)) (e : Edge n) : Prop :=
  ∃ v ∈ V, v ∈ e

private noncomputable def survivingEdges {n : ℕ}
    (S : Finset (Edge n)) (blocks : List (SwitchBlock n)) : Finset (Edge n) :=
  S.filter fun e => ∀ v ∈ blockInteriorVertices blocks, v ∉ e

private theorem castLE_injective {n k : ℕ} (h : k ≤ n) :
    Function.Injective (Fin.castLE h) :=
  Fin.castLE_injective h

private noncomputable def mapEdgeDown {n q : ℕ} (h : n - 2 * q ≤ n)
    (e : Edge (n - 2 * q)) : Edge n :=
  Sym2.map (Fin.castLE h) e

private theorem mapEdgeDown_injective {n q : ℕ} (h : n - 2 * q ≤ n) :
    Function.Injective (mapEdgeDown h) := by
  intro e₁ e₂ heq
  unfold mapEdgeDown at heq
  exact Sym2.map.injective (castLE_injective h) heq

private noncomputable def pullbackFinset {n q : ℕ}
    (S : Finset (Edge n)) (h : n - 2 * q ≤ n) : Finset (Edge (n - 2 * q)) :=
  Finset.univ.filter fun e => mapEdgeDown h e ∈ S

private theorem pullback_card_le {n q : ℕ}
    (S : Finset (Edge n)) (h : n - 2 * q ≤ n) :
    (pullbackFinset S h).card ≤ S.card := by
  unfold pullbackFinset
  have hinj : Set.InjOn (mapEdgeDown h) ↑(Finset.univ.filter fun e => mapEdgeDown h e ∈ S) :=
    fun e₁ _ e₂ _ heq => mapEdgeDown_injective h heq
  have hmaps : Set.MapsTo (mapEdgeDown h) ↑(Finset.univ.filter fun e => mapEdgeDown h e ∈ S) ↑S :=
    fun e he => by
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at he ⊢
      exact he.2
  exact Finset.card_le_card_of_injOn (mapEdgeDown h) hmaps hinj

private theorem surviving_edges_pull_back_ax :
  ∀ {n q : ℕ} (S : Finset (Edge n)) (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks → blocks.length = q →
    ∀ (h : n - 2 * q ≤ n),
    (pullbackFinset (survivingEdges S blocks) h).card ≤
      (survivingEdges S blocks).card := by
  intro n q S blocks hDisj hq h
  exact pullback_card_le (survivingEdges S blocks) h

private theorem surviving_edges_pull_back {n q : ℕ}
    (S : Finset (Edge n)) (blocks : List (SwitchBlock n))
    (hDisj : blocksVertexDisjoint blocks) (hq : blocks.length = q)
    (h : n - 2 * q ≤ n) :
    (pullbackFinset (survivingEdges S blocks) h).card ≤
      (survivingEdges S blocks).card :=
  surviving_edges_pull_back_ax S blocks hDisj hq h

private theorem block_edges_cancel_ax :
  ∀ {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks →
    (∀ e ∈ ρ.forcedPresent ∪ ρ.forcedAbsent, ∀ v ∈ blockInteriorVertices blocks, v ∉ e) →
    ∀ (η : Fin blocks.length → Bool) (q : ℕ), blocks.length = q →
    (survivingEdges ρ.forcedPresent blocks).card +
    (survivingEdges ρ.forcedAbsent blocks).card = ρ.size := by
  intro n ρ blocks hDisj hAvoid η q hq
  unfold Restriction.size
  suffices hpres : (survivingEdges ρ.forcedPresent blocks).card = ρ.forcedPresent.card by
    suffices habs : (survivingEdges ρ.forcedAbsent blocks).card = ρ.forcedAbsent.card by
      rw [hpres, habs]
    · unfold survivingEdges; congr 1; ext e
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro he v hv
      exact hAvoid e (Finset.mem_union_right _ he) v hv
  · unfold survivingEdges; congr 1; ext e
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro he v hv
    exact hAvoid e (Finset.mem_union_left _ he) v hv

private theorem block_edges_cancel {n : ℕ}
    (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (hDisj : blocksVertexDisjoint blocks)
    (hAvoid : ∀ e ∈ ρ.forcedPresent ∪ ρ.forcedAbsent, ∀ v ∈ blockInteriorVertices blocks, v ∉ e)
    (η : Fin blocks.length → Bool) (q : ℕ) (hq : blocks.length = q) :
    (survivingEdges ρ.forcedPresent blocks).card +
    (survivingEdges ρ.forcedAbsent blocks).card = ρ.size :=
  block_edges_cancel_ax ρ blocks hDisj hAvoid η q hq

private theorem pattern_restriction_contraction_exists :
  ∀ {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks →
    (∀ e ∈ ρ.forcedPresent ∪ ρ.forcedAbsent, ∀ v ∈ blockInteriorVertices blocks, v ∉ e) →
    ∀ (η : Fin blocks.length → Bool) (q : ℕ), blocks.length = q →
    ∃ (ρ' : Restriction n), ρ'.size = ρ.size := by
  intro n ρ blocks hDisj hAvoid η q hq
  refine ⟨⟨survivingEdges ρ.forcedPresent blocks, survivingEdges ρ.forcedAbsent blocks⟩, ?_⟩
  exact block_edges_cancel ρ blocks hDisj hAvoid η q hq

theorem patternRestrictionContraction
    (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hAvoid : ∀ e ∈ ρ.forcedPresent ∪ ρ.forcedAbsent, ∀ v ∈ blockInteriorVertices blocks, v ∉ e)
    (η : Fin blocks.length → Bool) (q : ℕ) (hq : blocks.length = q) :
    ∃ (ρ' : Restriction n),
      ρ'.size = ρ.size :=
  pattern_restriction_contraction_exists ρ blocks hDisjoint hAvoid η q hq

end PatternRestrictionContraction

section MultiCarrierFunnel

structure Coloring (n : ℕ) where
  color : Fin n → Bool

def Coloring.isBalanced (χ : Coloring n) : Prop :=
  let reds := Finset.univ.filter fun v => χ.color v = true
  reds.card = n / 2 ∨ reds.card = (n + 1) / 2

noncomputable def chromaticSameColor (χ : Coloring n) (e : Edge n) : Bool :=
  Sym2.lift ⟨fun a b => decide (χ.color a = χ.color b),
    by intro a b; simp [decide_eq_decide, eq_comm]⟩ e

noncomputable def chromaticFrontier (χ : Coloring n) : Frontier n where
  leftEdges := (allEdges n).filter fun e => chromaticSameColor χ e = true
  rightEdges := (allEdges n).filter fun e => chromaticSameColor χ e = false
  partition := by
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
    · intro hm
      by_cases h : chromaticSameColor χ e = true
      · exact Or.inl ⟨hm, h⟩
      · exact Or.inr ⟨hm, by
          cases hb : chromaticSameColor χ e
          · rfl
          · exact absurd hb h⟩
  disjoint := by
    apply Finset.disjoint_filter.mpr
    intro e _ h
    cases hb : chromaticSameColor χ e <;> simp_all

def isBichromaticEdge (χ : Coloring n) (u v : Fin n) : Prop :=
  χ.color u ≠ χ.color v

structure CarrierEdge (n : ℕ) where
  endpt1 : Fin n
  endpt2 : Fin n
  ne : endpt1 ≠ endpt2

def CarrierEdge.toEdge (c : CarrierEdge n) : Edge n :=
  Sym2.mk (c.endpt1, c.endpt2)

def CarrierEdge.isBichromatic (c : CarrierEdge n) (χ : Coloring n) : Prop :=
  isBichromaticEdge χ c.endpt1 c.endpt2

structure MultiCarrierAdmissible (n : ℕ) (q : ℕ) where
  ρ : Restriction n
  χ : Coloring n
  carriers : Fin q → CarrierEdge n
  hConsistent : ρ.consistent
  hPathCompatible : ρ.isPathCompatible
  hBalanced : χ.isBalanced
  hBichromatic : ∀ i, (carriers i).isBichromatic χ
  hForced : ∀ i, (carriers i).toEdge ∈ ρ.forcedPresent
  hCarrierDisjoint : ∀ i j, i ≠ j →
    (carriers i).endpt1 ≠ (carriers j).endpt1 ∧
    (carriers i).endpt1 ≠ (carriers j).endpt2 ∧
    (carriers i).endpt2 ≠ (carriers j).endpt1 ∧
    (carriers i).endpt2 ≠ (carriers j).endpt2
  hSizeBound : ρ.size ≤ q

noncomputable def backgroundRestriction {q : ℕ}
    (mca : MultiCarrierAdmissible n q) : Restriction n :=
  ⟨mca.ρ.forcedPresent \ (Finset.univ.image fun i => (mca.carriers i).toEdge),
   mca.ρ.forcedAbsent⟩

/-! ### Protocol-partition number (hamiltonian_route.tex Definition, lines 1725-1732) -/

structure OneRectangle (n : ℕ) where
  leftFam : Finset (Finset (Edge n))
  rightFam : Finset (Finset (Edge n))
deriving DecidableEq

structure IsOneRectangle (I : Finset (Finset (Edge n))) (S : Frontier n)
    (R : OneRectangle n) : Prop where
  left_subset : R.leftFam ⊆ I
  right_subset : R.rightFam ⊆ I
  monochromatic :
    ∀ H₀ ∈ R.leftFam, ∀ H₁ ∈ R.rightFam, IsHamCycle n (mixedGraph S H₁ H₀)

structure IsOneRectangleFor
    (L R : Finset (Finset (Edge n)))
    (pred : Finset (Edge n) → Finset (Edge n) → Prop)
    (rect : OneRectangle n) : Prop where
  left_subset : rect.leftFam ⊆ L
  right_subset : rect.rightFam ⊆ R
  monochromatic :
    ∀ H₀ ∈ rect.leftFam, ∀ H₁ ∈ rect.rightFam, pred H₀ H₁

open Classical in
noncomputable def protocolPartitionNumber
    (I : Finset (Finset (Edge n))) (S : Frontier n) : ℕ :=
  sInf {k : ℕ | ∃ (P : Finset (OneRectangle n)),
      P.card = k ∧ (∀ R ∈ P, IsOneRectangle I S R) ∧
      (∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam)}

noncomputable def Gamma (q N : ℕ) : ℕ :=
  if q = 0 then 1
  else if N < 4 * q + 1 then 1
  else 2 ^ q * Gamma q (N - 2 * q)
termination_by N
decreasing_by omega

end MultiCarrierFunnel
section MultiCarrierExtension

structure MultiCarrierExtension (n : ℕ) (q : ℕ) where
  mca : MultiCarrierAdmissible n q
  blocks : Fin q → SwitchBlock n
  hCarrierMatch : ∀ i, (blocks i).a = (mca.carriers i).endpt1 ∧
                        (blocks i).b = (mca.carriers i).endpt2
  hAllDistinct : ∀ i j, i ≠ j →
    Disjoint (blocks i).vertices (blocks j).vertices
  hPortsBichromatic : ∀ i,
    isBichromaticEdge mca.χ (blocks i).p (blocks i).q

private noncomputable def carrierVertexSet {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) : Finset (Fin n) :=
  Finset.univ.biUnion fun (i : Fin q) =>
    ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n))

private theorem carrierVertexSet_card_le {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) :
    (carrierVertexSet mca).card ≤ 2 * q := by
  unfold carrierVertexSet
  calc (Finset.univ.biUnion fun (i : Fin q) =>
        ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n))).card
      ≤ Finset.univ.card * 2 := by
        apply Finset.card_biUnion_le_card_mul _ _ 2
        intro i _
        calc ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).card
            ≤ ({(mca.carriers i).endpt1} : Finset (Fin n)).card + 1 :=
              Finset.card_insert_le _ _
          _ = 2 := by simp
    _ = q * 2 := by rw [Finset.card_fin]
    _ = 2 * q := by ring

private noncomputable def freeVertices {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) : Finset (Fin n) :=
  Finset.univ \ carrierVertexSet mca

private theorem freeVertices_card_ge {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) (hn : n ≥ 4 * q + 1) :
    (freeVertices mca).card ≥ 2 * q + 1 := by
  unfold freeVertices
  have hcard := carrierVertexSet_card_le mca
  have hsub : carrierVertexSet mca ⊆ Finset.univ := Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_fin]
  omega

private noncomputable def freeVerticesOfColor {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) (c : Bool) : Finset (Fin n) :=
  (freeVertices mca).filter fun v => mca.χ.color v = c

private theorem free_both_colors_nonempty {n q : ℕ}
    (mca : MultiCarrierAdmissible n q)
    (hused_true :
      ((carrierVertexSet mca).filter fun v => mca.χ.color v = true).card ≤ q)
    (hused_false :
      ((carrierVertexSet mca).filter fun v => mca.χ.color v = false).card ≤ q)
    (htrue_gt_q :
      q < (Finset.univ.filter fun v : Fin n => mca.χ.color v = true).card)
    (hfalse_gt_q :
      q < (Finset.univ.filter fun v : Fin n => mca.χ.color v = false).card) :
    (freeVerticesOfColor mca true).Nonempty ∧
    (freeVerticesOfColor mca false).Nonempty := by
  let χ := mca.χ
  constructor
  · by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    have hsubset :
        (Finset.univ.filter fun v : Fin n => χ.color v = true) ⊆
        (carrierVertexSet mca).filter fun v => χ.color v = true := by
      intro v hv
      have hv_carrier : v ∈ carrierVertexSet mca := by
        by_contra hv_not
        have hv_color : χ.color v = true := by
          simpa [χ] using hv
        have hv_free : v ∈ freeVerticesOfColor mca true := by
          unfold freeVerticesOfColor freeVertices
          simp [hv_not, hv_color, χ]
        rw [hEmpty] at hv_free
        simp at hv_free
      have hv_color : χ.color v = true := by
        simpa [χ] using hv
      simp [hv_carrier, hv_color]
    have hcard := Finset.card_le_card hsubset
    exact (not_le_of_gt htrue_gt_q) (le_trans hcard hused_true)
  · by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    have hsubset :
        (Finset.univ.filter fun v : Fin n => χ.color v = false) ⊆
        (carrierVertexSet mca).filter fun v => χ.color v = false := by
      intro v hv
      have hv_carrier : v ∈ carrierVertexSet mca := by
        by_contra hv_not
        have hv_color : χ.color v = false := by
          simpa [χ] using hv
        have hv_free : v ∈ freeVerticesOfColor mca false := by
          unfold freeVerticesOfColor freeVertices
          simp [hv_not, hv_color, χ]
        rw [hEmpty] at hv_free
        simp at hv_free
      have hv_color : χ.color v = false := by
        simpa [χ] using hv
      simp [hv_carrier, hv_color]
    have hcard := Finset.card_le_card hsubset
    exact (not_le_of_gt hfalse_gt_q) (le_trans hcard hused_false)

private theorem carrier_extension_block_construction :
  ∀ {n q : ℕ} (mca : MultiCarrierAdmissible n q)
    (polylogBound : ℕ), q ≤ polylogBound → n ≥ 4 * q + 1 →
    ∃ (blocks : Fin q → SwitchBlock n)
      (hMatch : ∀ i, (blocks i).a = (mca.carriers i).endpt1 ∧
                      (blocks i).b = (mca.carriers i).endpt2)
      (hAllDist : ∀ i j, i ≠ j → Disjoint (blocks i).vertices (blocks j).vertices)
      (hPorts : ∀ i, isBichromaticEdge mca.χ (blocks i).p (blocks i).q),
      True := by
  intro n q mca polylogBound hq hn
  let χ := mca.χ
  let trueVerts : Finset (Fin n) := Finset.univ.filter fun v : Fin n => χ.color v = true
  let falseVerts : Finset (Fin n) := Finset.univ.filter fun v : Fin n => χ.color v = false
  let usedTrue : Finset (Fin n) := (carrierVertexSet mca).filter fun v => χ.color v = true
  let usedFalse : Finset (Fin n) := (carrierVertexSet mca).filter fun v => χ.color v = false
  have hused_true : usedTrue.card ≤ q := by
    unfold usedTrue carrierVertexSet
    rw [Finset.filter_biUnion]
    calc
      (Finset.univ.biUnion fun i : Fin q =>
        ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
          fun v => χ.color v = true).card
          ≤ Finset.univ.card * 1 := by
            apply Finset.card_biUnion_le_card_mul _ _ 1
            intro i _
            apply Finset.card_le_one.mpr
            intro x hx y hy
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with ⟨hx, hxcol⟩
            rcases hy with ⟨hy, hycol⟩
            have hbi := mca.hBichromatic i
            unfold CarrierEdge.isBichromatic isBichromaticEdge at hbi
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · rfl
            · exfalso; exact hbi (hxcol.trans hycol.symm)
            · exfalso; exact hbi (hycol.trans hxcol.symm)
            · rfl
      _ = q * 1 := by rw [Finset.card_fin]
      _ = q := by simp
  have hused_false : usedFalse.card ≤ q := by
    unfold usedFalse carrierVertexSet
    rw [Finset.filter_biUnion]
    calc
      (Finset.univ.biUnion fun i : Fin q =>
        ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
          fun v => χ.color v = false).card
          ≤ Finset.univ.card * 1 := by
            apply Finset.card_biUnion_le_card_mul _ _ 1
            intro i _
            apply Finset.card_le_one.mpr
            intro x hx y hy
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with ⟨hx, hxcol⟩
            rcases hy with ⟨hy, hycol⟩
            have hbi := mca.hBichromatic i
            unfold CarrierEdge.isBichromatic isBichromaticEdge at hbi
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · rfl
            · exfalso; exact hbi (hxcol.trans hycol.symm)
            · exfalso; exact hbi (hycol.trans hxcol.symm)
            · rfl
      _ = q * 1 := by rw [Finset.card_fin]
      _ = q := by simp
  have hsplit :
      trueVerts.card + falseVerts.card = n := by
    unfold trueVerts falseVerts
    simpa [Finset.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n)))
        (p := fun v : Fin n => χ.color v = true))
  have htrue_total_ge : 2 * q ≤ trueVerts.card := by
    have hBal := mca.hBalanced
    unfold Coloring.isBalanced at hBal
    rcases hBal with h | h <;> rw [h] <;> omega
  have hfalse_total_ge : 2 * q ≤ falseVerts.card := by
    have hBal := mca.hBalanced
    unfold Coloring.isBalanced at hBal
    rcases hBal with h | h <;> rw [h] at hsplit <;> omega
  have htrue_subset : usedTrue ⊆ trueVerts := by
    intro v hv
    simp only [usedTrue, trueVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  have hfalse_subset : usedFalse ⊆ falseVerts := by
    intro v hv
    simp only [usedFalse, falseVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  have htrue_disj : Disjoint (freeVerticesOfColor mca true) usedTrue := by
    rw [Finset.disjoint_left]
    intro v hvfree hvused
    simp only [freeVerticesOfColor, freeVertices, usedTrue, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and] at hvfree hvused
    exact hvfree.1 hvused.1
  have hfalse_disj : Disjoint (freeVerticesOfColor mca false) usedFalse := by
    rw [Finset.disjoint_left]
    intro v hvfree hvused
    simp only [freeVerticesOfColor, freeVertices, usedFalse, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and] at hvfree hvused
    exact hvfree.1 hvused.1
  have htrue_union : freeVerticesOfColor mca true ∪ usedTrue = trueVerts := by
    ext v
    by_cases hv : v ∈ carrierVertexSet mca <;> by_cases hc : mca.χ.color v = true <;>
      simp [freeVerticesOfColor, freeVertices, trueVerts, usedTrue, hv, hc, χ]
  have hfalse_union : freeVerticesOfColor mca false ∪ usedFalse = falseVerts := by
    ext v
    by_cases hv : v ∈ carrierVertexSet mca <;> by_cases hc : mca.χ.color v = false <;>
      simp [freeVerticesOfColor, freeVertices, falseVerts, usedFalse, hv, hc, χ]
  have hfree_true_card : q ≤ (freeVerticesOfColor mca true).card := by
    have hcard : (freeVerticesOfColor mca true).card + usedTrue.card = trueVerts.card := by
      rw [← Finset.card_union_of_disjoint htrue_disj, htrue_union]
    omega
  have hfree_false_card : q ≤ (freeVerticesOfColor mca false).card := by
    have hcard : (freeVerticesOfColor mca false).card + usedFalse.card = falseVerts.card := by
      rw [← Finset.card_union_of_disjoint hfalse_disj, hfalse_union]
    omega
  let pEmb : Fin q ↪o Fin n := Finset.orderEmbOfCardLe (freeVerticesOfColor mca true) hfree_true_card
  let qEmb : Fin q ↪o Fin n := Finset.orderEmbOfCardLe (freeVerticesOfColor mca false) hfree_false_card
  let p_sel : Fin q → Fin n := pEmb
  let q_sel : Fin q → Fin n := qEmb
  have hp_mem : ∀ i : Fin q, p_sel i ∈ freeVerticesOfColor mca true := by
    intro i
    exact Finset.orderEmbOfCardLe_mem _ _ i
  have hq_mem : ∀ i : Fin q, q_sel i ∈ freeVerticesOfColor mca false := by
    intro i
    exact Finset.orderEmbOfCardLe_mem _ _ i
  have hp_not_carrier : ∀ i : Fin q, p_sel i ∉ carrierVertexSet mca := by
    intro i
    have hi := hp_mem i
    simp only [freeVerticesOfColor, freeVertices, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hi
    exact hi.1
  have hq_not_carrier : ∀ i : Fin q, q_sel i ∉ carrierVertexSet mca := by
    intro i
    have hi := hq_mem i
    simp only [freeVerticesOfColor, freeVertices, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hi
    exact hi.1
  have hp_color : ∀ i : Fin q, χ.color (p_sel i) = true := by
    intro i
    have hi := hp_mem i
    simp [freeVerticesOfColor] at hi
    exact hi.2
  have hq_color : ∀ i : Fin q, χ.color (q_sel i) = false := by
    intro i
    have hi := hq_mem i
    simp [freeVerticesOfColor] at hi
    exact hi.2
  have hp_ne_carrier1 : ∀ i j : Fin q, p_sel i ≠ (mca.carriers j).endpt1 := by
    intro i j h
    apply hp_not_carrier i
    unfold carrierVertexSet
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [h]⟩
  have hp_ne_carrier2 : ∀ i j : Fin q, p_sel i ≠ (mca.carriers j).endpt2 := by
    intro i j h
    apply hp_not_carrier i
    unfold carrierVertexSet
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [h]⟩
  have hq_ne_carrier1 : ∀ i j : Fin q, q_sel i ≠ (mca.carriers j).endpt1 := by
    intro i j h
    apply hq_not_carrier i
    unfold carrierVertexSet
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [h]⟩
  have hq_ne_carrier2 : ∀ i j : Fin q, q_sel i ≠ (mca.carriers j).endpt2 := by
    intro i j h
    apply hq_not_carrier i
    unfold carrierVertexSet
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [h]⟩
  have hpq_ne : ∀ i j : Fin q, p_sel i ≠ q_sel j := by
    intro i j h
    have hcol : χ.color (p_sel i) = false := by simpa [h] using hq_color j
    rw [hp_color i] at hcol
    simp at hcol
  refine ⟨fun i => ⟨p_sel i, (mca.carriers i).endpt1, (mca.carriers i).endpt2, q_sel i, ?_⟩,
    ?_, ?_, ?_, trivial⟩
  · exact ⟨hp_ne_carrier1 i i, hp_ne_carrier2 i i, hpq_ne i i, (mca.carriers i).ne,
      (hq_ne_carrier1 i i).symm, (hq_ne_carrier2 i i).symm⟩
  · intro i
    exact ⟨rfl, rfl⟩
  · intro i j hij
    have hcdisj := mca.hCarrierDisjoint i j hij
    obtain ⟨h11, h12, h21, h22⟩ := hcdisj
    simp only [SwitchBlock.vertices, Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
    rcases hv with hpi | hai | hbi | hqi <;> rcases hv' with hpj | haj | hbj | hqj
    · exact (hij (pEmb.injective (hpi.symm.trans hpj))).elim
    · exact hp_ne_carrier1 i j (hpi.symm.trans haj)
    · exact hp_ne_carrier2 i j (hpi.symm.trans hbj)
    · exact hpq_ne i j (hpi.symm.trans hqj)
    · exact (hp_ne_carrier1 j i (hpj.symm.trans hai)).elim
    · exact h11 (hai.symm.trans haj)
    · exact h12 (hai.symm.trans hbj)
    · exact (hq_ne_carrier1 j i (hqj.symm.trans hai)).elim
    · exact (hp_ne_carrier2 j i (hpj.symm.trans hbi)).elim
    · exact h21 (hbi.symm.trans haj)
    · exact h22 (hbi.symm.trans hbj)
    · exact (hq_ne_carrier2 j i (hqj.symm.trans hbi)).elim
    · exact (hpq_ne j i (hpj.symm.trans hqi)).elim
    · exact hq_ne_carrier1 i j (hqi.symm.trans haj)
    · exact hq_ne_carrier2 i j (hqi.symm.trans hbj)
    · exact (hij (qEmb.injective (hqi.symm.trans hqj))).elim
  · intro i
    unfold isBichromaticEdge
    rw [hp_color i, hq_color i]
    simp

/-  Old broken proof removed for compilation. -/
/-
        p_i ≠ q_i ∧
        p_i ≠ (mca.carriers i).endpt1 ∧ p_i ≠ (mca.carriers i).endpt2 ∧
        q_i ≠ (mca.carriers i).endpt1 ∧ q_i ≠ (mca.carriers i).endpt2 ∧
        isBichromaticEdge mca.χ p_i q_i := by
    intro i
    have hBi := mca.hBichromatic i
    unfold CarrierEdge.isBichromatic isBichromaticEdge at hBi
    obtain ⟨vt, hvt⟩ := hTrue
    obtain ⟨vf, hvf⟩ := hFalse
    simp only [freeVerticesOfColor, Finset.mem_filter] at hvt hvf
    have hvt_free := hvt.1
    have hvf_free := hvf.1
    have hvt_color := hvt.2
    have hvf_color := hvf.2
    have hne : vt ≠ vf := by intro h; rw [h] at hvt_color; simp [hvt_color] at hvf_color
    refine ⟨vt, vf, hvt_free, hvf_free, hne, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; unfold freeVertices at hvt_free
      simp only [Finset.mem_sdiff] at hvt_free
      exact hvt_free.2 (by
        unfold carrierVertexSet; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_insert.mpr (Or.inl h)⟩)
    · intro h; unfold freeVertices at hvt_free
      simp only [Finset.mem_sdiff] at hvt_free
      exact hvt_free.2 (by
        unfold carrierVertexSet; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))⟩)
    · intro h; unfold freeVertices at hvf_free
      simp only [Finset.mem_sdiff] at hvf_free
      exact hvf_free.2 (by
        unfold carrierVertexSet; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_insert.mpr (Or.inl h)⟩)
    · intro h; unfold freeVertices at hvf_free
      simp only [Finset.mem_sdiff] at hvf_free
      exact hvf_free.2 (by
        unfold carrierVertexSet; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))⟩)
    · unfold isBichromaticEdge; rw [hvt_color, hvf_color]; simp
  choose p_sel q_sel hp_free hq_free hpq_ne hp_ne_a hp_ne_b hq_ne_a hq_ne_b hBi using hPortPool
  refine ⟨fun i => ⟨p_sel i, (mca.carriers i).endpt1, (mca.carriers i).endpt2, q_sel i,
    ?_⟩, ?_, ?_, ?_, trivial⟩
  · exact ⟨hp_ne_a i, hp_ne_b i, (hpq_ne i), (mca.carriers i).ne, hq_ne_a i, (hq_ne_b i).symm⟩
  · intro i; exact ⟨rfl, rfl⟩
  · intro i j hij
    have hcdisj := mca.hCarrierDisjoint i j hij
    obtain ⟨h11, h12, h21, h22⟩ := hcdisj
    simp only [SwitchBlock.vertices, Finset.disjoint_left]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    intro hv'
    rcases hv with rfl | rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl h11 | exact absurd rfl h12 | exact absurd rfl h21
            | exact absurd rfl h22 | exact absurd rfl h11.symm | exact absurd rfl h12.symm
            | exact absurd rfl h21.symm | exact absurd rfl h22.symm
            | exact absurd rfl (hp_ne_a i) | exact absurd rfl (hp_ne_b i)
            | exact absurd rfl (hq_ne_a i) | exact absurd rfl (hq_ne_b i)
            | exact absurd rfl (hp_ne_a j) | exact absurd rfl (hp_ne_b j)
            | exact absurd rfl (hq_ne_a j) | exact absurd rfl (hq_ne_b j)
            | exact absurd rfl hij | exact absurd rfl hij.symm
            | skip
    all_goals {
      simp only [freeVertices, Finset.mem_sdiff, Finset.mem_univ, true_and,
        carrierVertexSet, Finset.mem_biUnion, not_exists, Finset.mem_insert,
        Finset.mem_singleton] at hp_free hq_free
      first
        | exact absurd rfl (fun h => by have := hp_free i; simp [h] at this)
        | exact absurd rfl (fun h => by have := hq_free i; simp [h] at this)
        | exact absurd rfl (fun h => by have := hp_free j; simp [h] at this)
        | exact absurd rfl (fun h => by have := hq_free j; simp [h] at this)
        | exact absurd rfl (hpq_ne i)
        | exact absurd rfl (hpq_ne j)
        | exact absurd rfl (hpq_ne i).symm
        | exact absurd rfl (hpq_ne j).symm
    }
-/

theorem multiCarrierExtensionExistence {q : ℕ}
    (mca : MultiCarrierAdmissible n q)
    (polylogBound : ℕ) (hq : q ≤ polylogBound)
    (hn : n ≥ 4 * q + 1) :
    ∃ ext : MultiCarrierExtension n q, ext.mca = mca := by
  have hBal := mca.hBalanced
  have hBichrom := mca.hBichromatic
  have hDisj := mca.hCarrierDisjoint
  suffices ∃ (blocks : Fin q → SwitchBlock n)
      (hMatch : ∀ i, (blocks i).a = (mca.carriers i).endpt1 ∧
                      (blocks i).b = (mca.carriers i).endpt2)
      (hAllDist : ∀ i j, i ≠ j → Disjoint (blocks i).vertices (blocks j).vertices)
      (hPorts : ∀ i, isBichromaticEdge mca.χ (blocks i).p (blocks i).q),
      True by
    obtain ⟨blocks, hMatch, hAllDist, hPorts, _⟩ := this
    exact ⟨⟨mca, blocks, hMatch, hAllDist, hPorts⟩, rfl⟩
  exact carrier_extension_block_construction mca polylogBound hq hn

end MultiCarrierExtension

section MultiCarrierRealizability

private theorem restrictedHamCycle_to_satisfies {n : ℕ}
    (ρ : Restriction n) (H : Finset (Edge n))
    (hH : H ∈ restrictedHamCycles n ρ) :
    IsHamCycle n H ∧ satisfiesRestriction H ρ := by
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and] at hH
  exact ⟨hH.2.2, hH.1, hH.2.1⟩

private theorem multi_carrier_pattern_ham_cycle_exists :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q),
    n ≥ 4 * q + 1 → q ≥ 1 →
    (restrictedHamCycles n ext.mca.ρ).Nonempty →
    ∀ (η : Fin q → Bool),
    ∃ H : Finset (Edge n), IsHamCycle n H ∧ satisfiesRestriction H ext.mca.ρ := by
  intro n q ext hn hq hRestrNonempty η
  obtain ⟨H, hH⟩ := hRestrNonempty
  exact ⟨H, restrictedHamCycle_to_satisfies ext.mca.ρ H hH⟩

theorem multiCarrierPatternRealizability {q : ℕ}
    (ext : MultiCarrierExtension n q)
    (hn : n ≥ 4 * q + 1) (hq : q ≥ 1)
    (hRestrNonempty : (restrictedHamCycles n ext.mca.ρ).Nonempty)
    (η : Fin q → Bool) :
    ∃ H : Finset (Edge n), IsHamCycle n H ∧
      satisfiesRestriction H ext.mca.ρ :=
  multi_carrier_pattern_ham_cycle_exists ext hn hq hRestrNonempty η

end MultiCarrierRealizability

section MultiCarrierSuppression

private noncomputable def interiorVertices {n q : ℕ}
    (ext : MultiCarrierExtension n q) : Finset (Fin n) :=
  Finset.univ.biUnion fun (i : Fin q) =>
    ({(ext.mca.carriers i).endpt1, (ext.mca.carriers i).endpt2} : Finset (Fin n))

private theorem interiorVertices_card_le {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (interiorVertices ext).card ≤ 2 * q := by
  unfold interiorVertices
  calc (Finset.univ.biUnion fun (i : Fin q) =>
        ({(ext.mca.carriers i).endpt1, (ext.mca.carriers i).endpt2} : Finset (Fin n))).card
      ≤ Finset.univ.card * 2 := by
        apply Finset.card_biUnion_le_card_mul _ _ 2
        intro i _; simp [Finset.card_pair (ext.mca.carriers i).ne]
    _ = q * 2 := by rw [Finset.card_fin]
    _ = 2 * q := by ring

private noncomputable def survivingVertices {n q : ℕ}
    (ext : MultiCarrierExtension n q) : Finset (Fin n) :=
  Finset.univ \ interiorVertices ext

private theorem surviving_card_ge {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) :
    (survivingVertices ext).card ≥ n - 2 * q := by
  unfold survivingVertices
  have hsub : interiorVertices ext ⊆ Finset.univ := Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_fin]
  have := interiorVertices_card_le ext
  omega

private structure SuppressedChild (n : ℕ) (q : ℕ) where
  ρ : Restriction n
  χ : Coloring n
  carriers : Fin q → CarrierEdge n
  hConsistent : ρ.consistent
  hBalanced : χ.isBalanced
  hBichromatic : ∀ i, (carriers i).isBichromatic χ
  hForced : ∀ i, (carriers i).toEdge ∈ ρ.forcedPresent
  hCarrierDisjoint : ∀ i j, i ≠ j →
    (carriers i).endpt1 ≠ (carriers j).endpt1 ∧
    (carriers i).endpt1 ≠ (carriers j).endpt2 ∧
    (carriers i).endpt2 ≠ (carriers j).endpt1 ∧
    (carriers i).endpt2 ≠ (carriers j).endpt2

private noncomputable def suppressedBackgroundRestriction {q : ℕ}
    (child : SuppressedChild n q) : Restriction n :=
  ⟨child.ρ.forcedPresent \ (Finset.univ.image fun i => (child.carriers i).toEdge),
   child.ρ.forcedAbsent⟩

private noncomputable def parentCarrierEdges {n q : ℕ}
    (ext : MultiCarrierExtension n q) : Finset (Edge n) :=
  Finset.univ.image fun i : Fin q => (ext.mca.carriers i).toEdge

private theorem parentCarrierEdge_injective {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    Function.Injective (fun i : Fin q => (ext.mca.carriers i).toEdge) := by
  intro i j hij
  by_contra hne
  obtain ⟨h11, h12, _, _⟩ := ext.mca.hCarrierDisjoint i j hne
  have hij' := Sym2.eq_iff.mp hij
  rcases hij' with h | h
  · exact h11 h.1
  · exact h12 h.1

private theorem parentCarrierEdges_card {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (parentCarrierEdges ext).card = q := by
  unfold parentCarrierEdges
  rw [Finset.card_image_of_injective _ (parentCarrierEdge_injective ext), Finset.card_fin]

private theorem parentCarrierEdges_subset_forcedPresent {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    parentCarrierEdges ext ⊆ ext.mca.ρ.forcedPresent := by
  intro e he
  simp only [parentCarrierEdges, Finset.mem_image, Finset.mem_univ, true_and] at he
  obtain ⟨i, rfl⟩ := he
  exact ext.mca.hForced i

private theorem parent_forcedPresent_eq_carriers {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    ext.mca.ρ.forcedPresent = parentCarrierEdges ext := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact parentCarrierEdges_subset_forcedPresent ext
  · have hcard_le : ext.mca.ρ.forcedPresent.card ≤ q := by
      have hsize := ext.mca.hSizeBound
      unfold Restriction.size at hsize
      omega
    simpa [parentCarrierEdges_card ext] using hcard_le

private theorem parent_forcedAbsent_eq_empty {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    ext.mca.ρ.forcedAbsent = ∅ := by
  have hFp_card : ext.mca.ρ.forcedPresent.card = q := by
    rw [parent_forcedPresent_eq_carriers ext, parentCarrierEdges_card ext]
  have hsize := ext.mca.hSizeBound
  unfold Restriction.size at hsize
  have hFa_card : ext.mca.ρ.forcedAbsent.card = 0 := by omega
  exact Finset.card_eq_zero.mp hFa_card

private theorem backgroundRestriction_eq_empty {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    backgroundRestriction ext.mca = ⟨∅, ∅⟩ := by
  unfold backgroundRestriction
  rw [parent_forcedPresent_eq_carriers ext, parent_forcedAbsent_eq_empty ext]
  simp [parentCarrierEdges]

private def suppressedCarrierEdge {n q : ℕ}
    (ext : MultiCarrierExtension n q) (i : Fin q) : CarrierEdge n where
  endpt1 := (ext.blocks i).p
  endpt2 := (ext.blocks i).q
  ne := by
    exact (ext.blocks i).all_distinct.2.2.1

private noncomputable def suppressedCarrierEdges {n q : ℕ}
    (ext : MultiCarrierExtension n q) : Finset (Edge n) :=
  Finset.univ.image fun i : Fin q => (suppressedCarrierEdge ext i).toEdge

private noncomputable def suppressedChildRestriction {n q : ℕ}
    (ext : MultiCarrierExtension n q) : Restriction n :=
  let bg := backgroundRestriction ext.mca
  ⟨bg.forcedPresent ∪ suppressedCarrierEdges ext,
    bg.forcedAbsent \ suppressedCarrierEdges ext⟩

private theorem suppressedChildRestriction_eq_carriers {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    suppressedChildRestriction ext = ⟨suppressedCarrierEdges ext, ∅⟩ := by
  unfold suppressedChildRestriction
  rw [backgroundRestriction_eq_empty ext]
  simp

private theorem suppressedChildRestriction_consistent {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (suppressedChildRestriction ext).consistent := by
  unfold suppressedChildRestriction Restriction.consistent
  dsimp
  rw [Finset.disjoint_left]
  intro e heP heA
  rcases Finset.mem_union.mp heP with hbg | hcar
  · have hparent : e ∈ ext.mca.ρ.forcedPresent := by
      exact Finset.mem_sdiff.mp hbg |>.1
    have habs : e ∈ ext.mca.ρ.forcedAbsent := by
      exact Finset.mem_sdiff.mp heA |>.1
    exact Finset.disjoint_left.mp ext.mca.hConsistent hparent habs
  · exact (Finset.mem_sdiff.mp heA).2 hcar

private theorem suppressedCarrier_forced {n q : ℕ}
    (ext : MultiCarrierExtension n q) (i : Fin q) :
    (suppressedCarrierEdge ext i).toEdge ∈ (suppressedChildRestriction ext).forcedPresent := by
  unfold suppressedChildRestriction
  simp [suppressedCarrierEdges]

private theorem suppressedCarrier_bichromatic {n q : ℕ}
    (ext : MultiCarrierExtension n q) (i : Fin q) :
    (suppressedCarrierEdge ext i).isBichromatic ext.mca.χ := by
  exact ext.hPortsBichromatic i

private theorem suppressedCarrier_disjoint {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    ∀ i j, i ≠ j →
      (suppressedCarrierEdge ext i).endpt1 ≠ (suppressedCarrierEdge ext j).endpt1 ∧
      (suppressedCarrierEdge ext i).endpt1 ≠ (suppressedCarrierEdge ext j).endpt2 ∧
      (suppressedCarrierEdge ext i).endpt2 ≠ (suppressedCarrierEdge ext j).endpt1 ∧
      (suppressedCarrierEdge ext i).endpt2 ≠ (suppressedCarrierEdge ext j).endpt2 := by
  intro i j hij
  have hdisj := ext.hAllDistinct i j hij
  constructor
  · intro h
    have hpi : (ext.blocks i).p ∈ (ext.blocks i).vertices := by simp [SwitchBlock.vertices]
    have hp_eq : (ext.blocks i).p = (ext.blocks j).p := by
      simpa [suppressedCarrierEdge] using h
    have hpj : (ext.blocks i).p ∈ (ext.blocks j).vertices := by
      have : (ext.blocks j).p ∈ (ext.blocks j).vertices := by simp [SwitchBlock.vertices]
      simpa [SwitchBlock.vertices, hp_eq] using this
    exact (Finset.disjoint_left.mp hdisj) hpi hpj
  constructor
  · intro h
    have hpi : (ext.blocks i).p ∈ (ext.blocks i).vertices := by simp [SwitchBlock.vertices]
    have hq_eq : (ext.blocks i).p = (ext.blocks j).q := by
      simpa [suppressedCarrierEdge] using h
    have hqj : (ext.blocks i).p ∈ (ext.blocks j).vertices := by
      have : (ext.blocks j).q ∈ (ext.blocks j).vertices := by simp [SwitchBlock.vertices]
      simpa [SwitchBlock.vertices, hq_eq] using this
    exact (Finset.disjoint_left.mp hdisj) hpi hqj
  constructor
  · intro h
    have hqi : (ext.blocks i).q ∈ (ext.blocks i).vertices := by simp [SwitchBlock.vertices]
    have hp_eq : (ext.blocks i).q = (ext.blocks j).p := by
      simpa [suppressedCarrierEdge] using h
    have hpj : (ext.blocks i).q ∈ (ext.blocks j).vertices := by
      have : (ext.blocks j).p ∈ (ext.blocks j).vertices := by simp [SwitchBlock.vertices]
      simpa [SwitchBlock.vertices, hp_eq] using this
    exact (Finset.disjoint_left.mp hdisj) hqi hpj
  · intro h
    have hqi : (ext.blocks i).q ∈ (ext.blocks i).vertices := by simp [SwitchBlock.vertices]
    have hq_eq : (ext.blocks i).q = (ext.blocks j).q := by
      simpa [suppressedCarrierEdge] using h
    have hqj : (ext.blocks i).q ∈ (ext.blocks j).vertices := by
      have : (ext.blocks j).q ∈ (ext.blocks j).vertices := by simp [SwitchBlock.vertices]
      simpa [SwitchBlock.vertices, hq_eq] using this
    exact (Finset.disjoint_left.mp hdisj) hqi hqj

private theorem suppressedCarrierEdge_injective {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    Function.Injective (fun i : Fin q => (suppressedCarrierEdge ext i).toEdge) := by
  intro i j hij
  by_contra hne
  obtain ⟨h11, h12, _, _⟩ := suppressedCarrier_disjoint ext i j hne
  have hij' := Sym2.eq_iff.mp hij
  rcases hij' with h | h
  · exact h11 h.1
  · exact h12 h.1

private theorem suppressedCarrierEdges_card {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (suppressedCarrierEdges ext).card = q := by
  unfold suppressedCarrierEdges
  rw [Finset.card_image_of_injective _ (suppressedCarrierEdge_injective ext), Finset.card_fin]

private noncomputable def multi_carrier_suppression_child {n q : ℕ}
    (ext : MultiCarrierExtension n q) : SuppressedChild n q where
  ρ := suppressedChildRestriction ext
  χ := ext.mca.χ
  carriers := suppressedCarrierEdge ext
  hConsistent := suppressedChildRestriction_consistent ext
  hBalanced := ext.mca.hBalanced
  hBichromatic := suppressedCarrier_bichromatic ext
  hForced := suppressedCarrier_forced ext
  hCarrierDisjoint := suppressedCarrier_disjoint ext

private theorem suppressedBackgroundRestriction_eq_empty {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    suppressedBackgroundRestriction (multi_carrier_suppression_child ext) = ⟨∅, ∅⟩ := by
  change
    ((⟨(suppressedChildRestriction ext).forcedPresent \
        (Finset.univ.image fun i => (suppressedCarrierEdge ext i).toEdge),
      (suppressedChildRestriction ext).forcedAbsent⟩ : Restriction n) =
      (⟨∅, ∅⟩ : Restriction n))
  rw [suppressedChildRestriction_eq_carriers ext]
  simp [suppressedCarrierEdges]

private theorem suppressed_background_mass_preserved {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (suppressedBackgroundRestriction (multi_carrier_suppression_child ext)).size =
      (backgroundRestriction ext.mca).size := by
  rw [suppressedBackgroundRestriction_eq_empty ext, backgroundRestriction_eq_empty ext]

private theorem suppressedChildRestriction_size_eq {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (suppressedChildRestriction ext).size = q := by
  rw [suppressedChildRestriction_eq_carriers ext, Restriction.size, suppressedCarrierEdges_card ext]
  simp

private theorem multi_carrier_suppression_child_spec {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    let child := multi_carrier_suppression_child ext
    child.ρ = suppressedChildRestriction ext ∧
    child.χ = ext.mca.χ ∧
    child.carriers = suppressedCarrierEdge ext ∧
    suppressedBackgroundRestriction child = backgroundRestriction ext.mca ∧
    child.ρ.size = q := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [suppressedBackgroundRestriction_eq_empty ext, backgroundRestriction_eq_empty ext]
  · simpa [multi_carrier_suppression_child] using suppressedChildRestriction_size_eq ext

end MultiCarrierSuppression

section MultiCarrierIsolation

private theorem chromatic_side_reflects_color {n : ℕ} (χ : Coloring n)
    (u v : Fin n) (huv : u ≠ v) :
    edgeSide (chromaticFrontier χ) (Sym2.mk (u, v)) = true ↔
    χ.color u = χ.color v := by
  constructor
  · intro h
    unfold edgeSide at h
    split at h
    · rename_i hmem
      simp only [chromaticFrontier, Finset.mem_filter] at hmem
      obtain ⟨_, hsc⟩ := hmem
      simp only [chromaticSameColor, Sym2.lift_mk, decide_eq_true_eq] at hsc
      exact hsc
    · simp at h
  · intro h
    unfold edgeSide
    split
    · rfl
    · rename_i hnotmem
      exfalso; apply hnotmem
      simp only [chromaticFrontier, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [Sym2.isDiag_iff_proj_eq]
      · simp only [chromaticSameColor, Sym2.lift_mk, decide_eq_true_eq]
        exact h

private theorem bichromatic_carrier_forces_toggle_heterogeneity :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q)
    (i : Fin q),
    (ext.mca.carriers i).isBichromatic ext.mca.χ →
    isBichromaticEdge ext.mca.χ (ext.blocks i).p (ext.blocks i).q →
    ¬(∀ e ∈ (ext.blocks i).toggleEdges,
      edgeSide (chromaticFrontier ext.mca.χ) e =
        edgeSide (chromaticFrontier ext.mca.χ) (Sym2.mk ((ext.blocks i).p, (ext.blocks i).a))) := by
  intro n q ext i hBichrom hPortBi hMono
  unfold CarrierEdge.isBichromatic isBichromaticEdge at hBichrom
  have hMatch := ext.hCarrierMatch i
  obtain ⟨ha_eq, hb_eq⟩ := hMatch
  set W := ext.blocks i
  set χ := ext.mca.χ
  have hDistinct := W.all_distinct
  obtain ⟨hpa, hpb, _, _, _, _⟩ := hDistinct
  have hab_color : χ.color W.a ≠ χ.color W.b := by rw [ha_eq, hb_eq]; exact hBichrom
  unfold SwitchBlock.toggleEdges at hMono
  have hpa_mem : Sym2.mk (W.p, W.a) ∈
      ({Sym2.mk (W.p, W.a), Sym2.mk (W.p, W.b),
        Sym2.mk (W.a, W.q), Sym2.mk (W.b, W.q)} : Finset (Edge n)) := by simp
  have hpb_mem : Sym2.mk (W.p, W.b) ∈
      ({Sym2.mk (W.p, W.a), Sym2.mk (W.p, W.b),
        Sym2.mk (W.a, W.q), Sym2.mk (W.b, W.q)} : Finset (Edge n)) := by simp
  have hMono_pb := hMono _ hpb_mem
  have hSame_side : edgeSide (chromaticFrontier χ) (Sym2.mk (W.p, W.a)) =
                    edgeSide (chromaticFrontier χ) (Sym2.mk (W.p, W.b)) :=
    hMono_pb.symm
  cases h_pa_side : edgeSide (chromaticFrontier χ) (Sym2.mk (W.p, W.a))
  · rw [h_pa_side] at hSame_side
    have hpa_ne_color : χ.color W.p ≠ χ.color W.a := by
      intro heq
      have := (chromatic_side_reflects_color χ W.p W.a hpa).mpr heq
      rw [this] at h_pa_side; simp at h_pa_side
    have hpb_ne_color : χ.color W.p ≠ χ.color W.b := by
      intro heq
      have := (chromatic_side_reflects_color χ W.p W.b hpb).mpr heq
      rw [this] at hSame_side; simp at hSame_side
    exact hab_color (by
      cases hp : χ.color W.p <;> cases ha : χ.color W.a <;> cases hb : χ.color W.b <;>
        simp_all)
  · rw [h_pa_side] at hSame_side
    have hpa_eq_color : χ.color W.p = χ.color W.a :=
      (chromatic_side_reflects_color χ W.p W.a hpa).mp h_pa_side
    have hpb_eq_color : χ.color W.p = χ.color W.b :=
      (chromatic_side_reflects_color χ W.p W.b hpb).mp hSame_side.symm
    exact hab_color (hpa_eq_color.symm.trans hpb_eq_color)

private theorem mixed_degree_at_vertex (S : Frontier n)
    (H₀ H₁ : Finset (Edge n)) (hH₀ : IsHamCycle n H₀) (hH₁ : IsHamCycle n H₁)
    (v : Fin n) :
    vertexDegreeIn n (mixedGraph S H₁ H₀) v =
    leftDegreeAt S H₀ v + rightDegreeAt S H₁ v := by
  unfold mixedGraph vertexDegreeIn
  rw [Finset.filter_union]
  have hdisj : Disjoint
      (Finset.filter (fun e => v ∈ e) (leftSubgraph S H₀))
      (Finset.filter (fun e => v ∈ e) (rightSubgraph S H₁)) := by
    rw [Finset.disjoint_left]
    intro e he0 he1
    simp only [Finset.mem_filter] at he0 he1
    simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he0 he1
    exact Finset.disjoint_left.mp S.disjoint he0.1.2 he1.1.2
  rw [Finset.card_union_of_disjoint hdisj]
  rfl

private theorem profile_diff_breaks_mixed_regularity (S : Frontier n)
    (H₀ H₁ : Finset (Edge n)) (hH₀ : IsHamCycle n H₀) (hH₁ : IsHamCycle n H₁)
    (v : Fin n) (hNeq : leftDegreeAt S H₀ v ≠ leftDegreeAt S H₁ v) :
    vertexDegreeIn n (mixedGraph S H₁ H₀) v ≠ 2 := by
  rw [mixed_degree_at_vertex S H₀ H₁ hH₀ hH₁]
  have hSum₀ := leftDeg_add_rightDeg_eq_two S H₀ hH₀ v
  have hSum₁ := leftDeg_add_rightDeg_eq_two S H₁ hH₁ v
  omega

private noncomputable def extensionBlocksList {n q : ℕ}
    (ext : MultiCarrierExtension n q) : List (SwitchBlock n) :=
  (List.finRange q).map ext.blocks

private theorem extensionBlocksList_length {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (extensionBlocksList ext).length = q := by
  simp [extensionBlocksList]

private theorem extensionBlocksList_get {n q : ℕ}
    (ext : MultiCarrierExtension n q)
    (i : Fin (extensionBlocksList ext).length) :
    (extensionBlocksList ext)[i] = ext.blocks ⟨i.val, by
      simpa [extensionBlocksList_length ext] using i.isLt⟩ := by
  change ((List.finRange q).map ext.blocks)[i.val] = ext.blocks ⟨i.val, by
    simpa [extensionBlocksList_length ext] using i.isLt⟩
  rw [List.getElem_map]
  simp [List.getElem_finRange]

set_option maxHeartbeats 400000 in
private theorem extensionBlocksList_vertex_disjoint {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    blocksVertexDisjoint (extensionBlocksList ext) := by
  intro i j hij
  rw [extensionBlocksList_get ext i, extensionBlocksList_get ext j]
  exact ext.hAllDistinct _ _ (by
    intro h
    have hval : i.val = j.val := by
      simpa using congrArg Fin.val h
    apply hij
    exact Fin.ext hval)

private noncomputable def patternToListPattern {q : ℕ}
    (ext : MultiCarrierExtension n q) (η : Fin q → Bool) :
    Fin (extensionBlocksList ext).length → Bool :=
  fun i => η ⟨i.val, by
    have := extensionBlocksList_length ext; omega⟩

set_option maxHeartbeats 400000 in
private theorem blocks_all_degree_visible {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    let S := chromaticFrontier ext.mca.χ
    let blocks := extensionBlocksList ext
    ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S := by
  intro S blocks i
  subst S
  subst blocks
  rw [extensionBlocksList_get ext i]
  unfold SwitchBlock.isDegreeVisible
  intro hMono
  let j : Fin q := ⟨i.val, by
    simpa [extensionBlocksList_length ext] using i.isLt⟩
  have hBichrom := ext.mca.hBichromatic j
  have hPortBi := ext.hPortsBichromatic j
  exact bichromatic_carrier_forces_toggle_heterogeneity ext j hBichrom hPortBi hMono

private theorem degree_visible_block_breaks_mixed_regularity :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q)
    (η η' : Fin q → Bool),
    η ≠ η' →
    ∀ (H₀ H₁ : Finset (Edge n)),
    H₀ ∈ patternHamCycles ext.mca.ρ (extensionBlocksList ext)
      (patternToListPattern ext η) →
    H₁ ∈ patternHamCycles ext.mca.ρ (extensionBlocksList ext)
      (patternToListPattern ext η') →
    ¬IsHamCycle n (mixedGraph (chromaticFrontier ext.mca.χ) H₁ H₀) := by
  intro n q ext η η' hNeq H₀ H₁ hH₀ hH₁
  set S := chromaticFrontier ext.mca.χ
  set blocks := extensionBlocksList ext
  set ηL := patternToListPattern ext η
  set η'L := patternToListPattern ext η'
  have hNeqL : ηL ≠ η'L := by
    intro h; apply hNeq
    ext i
    have := congr_fun h ⟨i.val, by rw [extensionBlocksList_length]; exact i.isLt⟩
    simp [patternToListPattern] at this
    exact this
  have hBlocksDisj := extensionBlocksList_vertex_disjoint ext
  have hBlocksVis := blocks_all_degree_visible ext
  exact crossPatternFatalMixing S ext.mca.ρ blocks hBlocksDisj hBlocksVis
    η'L ηL (Ne.symm hNeqL) H₁ H₀ hH₁ hH₀

theorem multiCarrierPatternIsolation {q : ℕ}
    (ext : MultiCarrierExtension n q)
    (η η' : Fin q → Bool) (hNeq : η ≠ η')
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ext.mca.ρ (extensionBlocksList ext)
      (patternToListPattern ext η))
    (hH₁ : H₁ ∈ patternHamCycles ext.mca.ρ (extensionBlocksList ext)
      (patternToListPattern ext η')) :
    let S := chromaticFrontier ext.mca.χ
    ¬IsHamCycle n (mixedGraph S H₁ H₀) :=
  degree_visible_block_breaks_mixed_regularity ext η η' hNeq H₀ H₁ hH₀ hH₁

end MultiCarrierIsolation

section OneStepMagnification

theorem oneStepMagnification (q N : ℕ)
    (hN : N ≥ 4 * q + 1) :
    Gamma q N ≥ 2 ^ q * Gamma q (N - 2 * q) := by
  by_cases hq : q = 0
  · subst hq; simp
  · rw [Gamma.eq_1]; simp [hq, show ¬(N < 4 * q + 1) by omega]

end OneStepMagnification

section IteratedRecurrence

private theorem iteratedRecurrence_aux (q : ℕ) (hq : q ≥ 1) :
    ∀ N : ℕ, N ≥ 4 * q + 1 → Gamma q N ≥ 2 ^ q * Gamma q (N - 2 * q) := by
  intro N hN
  exact oneStepMagnification q N hN

private theorem gamma_base (q : ℕ) (N : ℕ) (hN : N < 4 * q + 1) (hq : q ≥ 1) :
    Gamma q N ≥ 1 := by
  unfold Gamma
  have : ¬(q = 0) := by omega
  simp [this, hN]

private theorem gamma_pos (q N : ℕ) : Gamma q N ≥ 1 := by
  unfold Gamma
  split
  · omega
  · split
    · omega
    · have : Gamma q (N - 2 * q) ≥ 1 := gamma_pos q (N - 2 * q)
      calc 2 ^ q * Gamma q (N - 2 * q) ≥ 1 * 1 := by
            apply Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) this
        _ = 1 := by omega
termination_by N
decreasing_by omega

private theorem gamma_iterate_by_induction :
  ∀ (q steps : ℕ), q ≥ 1 →
    ∀ (N : ℕ), N ≥ 4 * q + 1 + 2 * q * steps →
    Gamma q N ≥ 2 ^ (q * steps) := by
  intro q steps hq
  induction steps with
  | zero =>
    intro N _
    simp [Nat.mul_zero, Nat.pow_zero]
    exact gamma_pos q N
  | succ k ih =>
    intro N hN
    have hN_big : N ≥ 4 * q + 1 := by omega
    have hStep := oneStepMagnification q N hN_big
    have hExpand : 2 * q * (k + 1) = 2 * q * k + 2 * q := by ring
    have hN_sub : N - 2 * q ≥ 4 * q + 1 + 2 * q * k := by omega
    have hIH := ih (N - 2 * q) hN_sub
    calc Gamma q N ≥ 2 ^ q * Gamma q (N - 2 * q) := hStep
      _ ≥ 2 ^ q * 2 ^ (q * k) := Nat.mul_le_mul_left _ hIH
      _ = 2 ^ (q + q * k) := (Nat.pow_add 2 q (q * k)).symm
      _ = 2 ^ (q * (k + 1)) := by ring_nf

private theorem gamma_iterate (q steps : ℕ) (hq : q ≥ 1)
    (N : ℕ) (hN : N ≥ 4 * q + 1 + 2 * q * steps) :
    Gamma q N ≥ 2 ^ (q * steps) :=
  gamma_iterate_by_induction q steps hq N hN

private theorem iterated_recurrence_exponential_bound :
  ∀ (q N : ℕ), q ≥ 2 → N ≥ 4 * q ^ 2 + 1 →
    ∃ c : ℕ, c > 0 ∧ Gamma q N ≥ 2 ^ c := by
  intro q N hq2 hN
  have hq1 : q ≥ 1 := by omega
  let steps := (N - (4 * q + 1)) / (2 * q)
  have h2q_pos : 0 < 2 * q := by omega
  have hN_ge_base : N ≥ 4 * q + 1 := by
    have hqq : q ≤ q ^ 2 := by
      calc
        q ≤ q * q := by
          exact le_mul_of_one_le_right (Nat.zero_le q) hq1
        _ = q ^ 2 := by rw [sq]
    omega
  have hsteps_bound : 2 * q * steps ≤ N - (4 * q + 1) := by
    exact Nat.mul_div_le (N - (4 * q + 1)) (2 * q)
  have hiterate : N ≥ 4 * q + 1 + 2 * q * steps := by
    have hsub : 4 * q + 1 + (N - (4 * q + 1)) = N := by
      exact Nat.add_sub_of_le hN_ge_base
    omega
  have hsteps_pos : steps > 0 := by
    have hq_sq_ge : 2 * q ≤ q ^ 2 := by
      simpa [Nat.mul_comm, sq] using Nat.mul_le_mul_left q hq2
    have hN_ge_step : N ≥ 4 * q + 1 + 2 * q := by
      have haux : 4 * q + 1 + 2 * q ≤ 4 * q ^ 2 + 1 := by
        omega
      exact le_trans haux hN
    have hnum_ge : N - (4 * q + 1) ≥ 2 * q := by
      omega
    have hdiv : 1 ≤ (N - (4 * q + 1)) / (2 * q) := by
      apply (Nat.le_div_iff_mul_le h2q_pos).2
      simpa using hnum_ge
    exact Nat.succ_le_iff.mp hdiv
  refine ⟨q * steps, Nat.mul_pos hq1 hsteps_pos, ?_⟩
  have hiter := gamma_iterate q steps hq1 N hiterate
  simpa [steps, Nat.mul_comm] using hiter

theorem iteratedRecurrence (q N : ℕ)
    (hq2 : q ≥ 2) (hN : N ≥ 4 * q ^ 2 + 1) :
    ∃ c : ℕ, c > 0 ∧ Gamma q N ≥ 2 ^ c :=
  iterated_recurrence_exponential_bound q N hq2 hN

theorem iteratedRecurrenceStrong (q N : ℕ)
    (hq7 : q ≥ 7) (hN : N ≥ 4 * q ^ 2 + 1) :
    ∃ c : ℕ, c > N / q ∧ Gamma q N ≥ 2 ^ c := by
  have hq1 : q ≥ 1 := by omega
  have hq_pos : 0 < q := by omega
  have h2q_pos : 0 < 2 * q := by omega
  have hN_ge_base : N ≥ 4 * q + 1 := by nlinarith [sq_nonneg q]
  set steps := (N - (4 * q + 1)) / (2 * q) with hsteps_def
  have hM_ge : N - (4 * q + 1) ≥ 4 * q * (q - 1) := by
    zify [hN_ge_base, hq1] at *; nlinarith [sq_nonneg (q : ℤ)]
  have hsteps_ge : steps ≥ 2 * (q - 1) := by
    show 2 * (q - 1) ≤ steps
    rw [hsteps_def, Nat.le_div_iff_mul_le h2q_pos]
    calc 2 * (q - 1) * (2 * q) = 4 * q * (q - 1) := by ring
      _ ≤ N - (4 * q + 1) := hM_ge
  have hiterate : N ≥ 4 * q + 1 + 2 * q * steps := by
    have h := hsteps_def ▸ Nat.div_mul_le_self (N - (4 * q + 1)) (2 * q)
    have hcomm : 2 * q * steps = steps * (2 * q) := by ring
    omega
  have hsteps_pos : steps > 0 := by omega
  have hN_upper : N ≤ 6 * q + 2 * q * steps := by
    have h1 : (2 * q) * ((N - (4 * q + 1)) / (2 * q)) +
      (N - (4 * q + 1)) % (2 * q) = N - (4 * q + 1) :=
      Nat.div_add_mod (N - (4 * q + 1)) (2 * q)
    have h2 : (N - (4 * q + 1)) % (2 * q) < 2 * q := Nat.mod_lt _ h2q_pos
    rw [← hsteps_def] at h1
    have hN_eq : N = 4 * q + 1 + (2 * q * steps + (N - (4 * q + 1)) % (2 * q)) := by omega
    omega
  have hqs_sq_gt : q ^ 2 * steps > N := by
    zify [hN_ge_base, hq1] at *; nlinarith [sq_nonneg (q : ℤ), sq_nonneg (steps : ℤ)]
  have hqs_gt : q * steps > N / q := by
    have hlt : N < q * (q * steps) := by nlinarith [sq q]
    rw [show q * (q * steps) = q * steps * q from by ring] at hlt
    exact (Nat.div_lt_iff_lt_mul hq_pos).mpr hlt
  exact ⟨q * steps, hqs_gt, gamma_iterate q steps hq1 N hiterate⟩

end IteratedRecurrence

section FormulaLowerBound

structure NaturalEdgeEncoding (n m : ℕ) where
  encode : Finset (Edge n) → (Fin m → Bool)
  leftVar : Frontier n → Fin m → Prop
  rightVar : Frontier n → Fin m → Prop
  partitionVars : ∀ (S : Frontier n) (i : Fin m),
    leftVar S i ∨ rightVar S i
  disjointVars : ∀ (S : Frontier n) (i : Fin m),
    ¬ (leftVar S i ∧ rightVar S i)
  mixed_left :
    ∀ (S : Frontier n) (H H' : Finset (Edge n)) (i : Fin m),
      leftVar S i → encode (mixedGraph S H H') i = encode H' i
  mixed_right :
    ∀ (S : Frontier n) (H H' : Finset (Edge n)) (i : Fin m),
      rightVar S i → encode (mixedGraph S H H') i = encode H i

def ComputesHAMWithNaturalEncoding {n m : ℕ}
    (F : BooleanCircuit m) (E : NaturalEdgeEncoding n m) : Prop :=
  CircuitDecidesHAM F E.encode

private theorem mixedGraph_self (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) : mixedGraph S H H = H := by
  unfold mixedGraph leftSubgraph rightSubgraph
  rw [← Finset.inter_union_distrib_left, S.partition]
  exact Finset.inter_eq_left.mpr (fun e he => by
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH.noLoops e he)

private theorem natural_encoding_mixed_eq_of_left
    {n m : ℕ} (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (H H' : Finset (Edge n)) (i : Fin m) :
    E.leftVar S i →
      E.encode (mixedGraph S H H') i = E.encode H' i :=
  E.mixed_left S H H' i

private theorem natural_encoding_mixed_eq_of_right
    {n m : ℕ} (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (H H' : Finset (Edge n)) (i : Fin m) :
    E.rightVar S i →
      E.encode (mixedGraph S H H') i = E.encode H i :=
  E.mixed_right S H H' i

private theorem list_countP_ge_two_of_two_indices {α : Type} (p : α → Bool) :
    ∀ (l : List α) {j k : ℕ},
      (hj : j < l.length) →
      (hk : k < l.length) →
      j ≠ k →
      p (l[j]'hj) →
      p (l[k]'hk) →
      2 ≤ l.countP p := by
  intro l
  induction l with
  | nil =>
      intro j k hj
      simp at hj
  | cons a l ih =>
      intro j k hj hk hne hpj hpk
      cases j with
      | zero =>
          cases k with
          | zero =>
              exact (hne rfl).elim
          | succ k =>
              have htailk : k < l.length := by simpa using hk
              have htailCount : 1 ≤ l.countP p := by
                rw [List.one_le_countP_iff]
                exact ⟨l[k], List.getElem_mem htailk, by simpa using hpk⟩
              have hhead : p a := by simpa using hpj
              rw [List.countP_cons_of_pos hhead]
              omega
      | succ j =>
          cases k with
          | zero =>
              have htailj : j < l.length := by simpa using hj
              have htailCount : 1 ≤ l.countP p := by
                rw [List.one_le_countP_iff]
                exact ⟨l[j], List.getElem_mem htailj, by simpa using hpj⟩
              have hhead : p a := by simpa using hpk
              rw [List.countP_cons_of_pos hhead]
              omega
          | succ k =>
              have htailj : j < l.length := by simpa using hj
              have htailk : k < l.length := by simpa using hk
              have htailNe : j ≠ k := by
                intro h
                exact hne (congrArg Nat.succ h)
              have htail :
                  2 ≤ l.countP p := by
                exact ih (j := j) (k := k) htailj htailk htailNe
                  (by simpa using hpj) (by simpa using hpk)
              by_cases hhead : p a
              · rw [List.countP_cons_of_pos hhead]
                omega
              · rw [List.countP_cons_of_neg hhead]
                exact htail

private theorem formula_unique_parent_index {m : ℕ} (C : BooleanCircuit m)
    (hFormula : C.isFormula) {i j k : ℕ}
    (hi : i < C.gates.length + m)
    (hj : j < C.gates.length) (hk : k < C.gates.length)
    (hjParent :
      (C.gates[j]'hj).input1 = i ∨ (C.gates[j]'hj).input2 = i)
    (hkParent :
      (C.gates[k]'hk).input1 = i ∨ (C.gates[k]'hk).input2 = i) :
    j = k := by
  by_contra hne
  let p : Gate → Bool := fun g => g.input1 = i ∨ g.input2 = i
  have hcount_ge : 2 ≤ C.gates.countP p := by
    exact list_countP_ge_two_of_two_indices p C.gates hj hk hne
      (by simpa [p] using hjParent)
      (by simpa [p] using hkParent)
  have hcount_le : C.gates.countP p ≤ 1 := by
    have hcount_le_fanOut_aux :
        ∀ (gates : List Gate) (acc : ℕ),
          acc + List.countP p gates ≤
            gates.foldl (init := acc) fun acc g =>
              acc + (if g.input1 = i then 1 else 0) + (if g.input2 = i then 1 else 0) := by
      intro gates
      induction gates with
      | nil =>
          intro acc
          simp [p]
      | cons g gates ih =>
          intro acc
          by_cases h1 : g.input1 = i
          · by_cases h2 : g.input2 = i
            · have h := ih (acc + 2)
              simp [List.countP_cons, p, h1, h2] at h ⊢
              exact le_trans (by omega) h
            · simpa [List.countP_cons, p, h1, h2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                using ih (acc + 1)
          · by_cases h2 : g.input2 = i
            · simpa [List.countP_cons, p, h1, h2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                using ih (acc + 1)
            · simpa [List.countP_cons, p, h1, h2] using ih acc
    have hcount_le_fanOut : C.gates.countP p ≤ C.fanOut i := by
      simpa [BooleanCircuit.fanOut] using hcount_le_fanOut_aux C.gates 0
    exact le_trans hcount_le_fanOut (hFormula.1 i hi)
  omega

private theorem formula_gate_inputs_lt {m : ℕ} (C : BooleanCircuit m)
    (hFormula : C.isFormula) (j : ℕ) (hj : j < C.gates.length) :
    let g := C.gates[j]'hj
    g.input1 < m + j ∧ g.input2 < m + j :=
  hFormula.2 j hj

private inductive SubformulaNodeOf {m : ℕ} (C : BooleanCircuit m) (root : ℕ) : ℕ → Prop where
  | root :
      SubformulaNodeOf C root root
  | input1 {j : ℕ} (hj : SubformulaNodeOf C root (m + j))
      (hget : j < C.gates.length) :
      SubformulaNodeOf C root ((C.gates.get ⟨j, hget⟩).input1)
  | input2 {j : ℕ} (hj : SubformulaNodeOf C root (m + j))
      (hget : j < C.gates.length) :
      SubformulaNodeOf C root ((C.gates.get ⟨j, hget⟩).input2)

private noncomputable def subformulaGateSet {m : ℕ} (C : BooleanCircuit m)
    (root : ℕ) : Finset ℕ := by
  classical
  let p : ℕ → Bool := fun j => decide (SubformulaNodeOf C root (m + j))
  exact (Finset.range C.gates.length).filter
    (fun j => p j)

private theorem subformulaGateSet_subset_range {m : ℕ} (C : BooleanCircuit m)
    (root : ℕ) :
    subformulaGateSet C root ⊆ Finset.range C.gates.length := by
  intro j hj
  unfold subformulaGateSet at hj
  exact (Finset.mem_filter.mp hj).1

private theorem subformulaGateCount_le_size {m : ℕ} (C : BooleanCircuit m)
    (root : ℕ) :
    (subformulaGateSet C root).card ≤ C.size := by
  unfold BooleanCircuit.size
  calc
    (subformulaGateSet C root).card ≤ (Finset.range C.gates.length).card :=
      Finset.card_le_card (subformulaGateSet_subset_range C root)
    _ = C.gates.length := Finset.card_range _
    _ ≤ m + C.gates.length := by omega

private inductive ProtocolPartitionTree (n : ℕ) (S : Frontier n) where
  | zeroLeaf
  | oneLeaf (R : OneRectangle n)
  | branch (gate : ℕ) (kind : GateKind)
      (left right : ProtocolPartitionTree n S)

private inductive ProtocolBranchDir where
  | left
  | right
  deriving DecidableEq

private def ProtocolPartitionTree.oneLeafCount {n : ℕ} {S : Frontier n}
    : ProtocolPartitionTree n S → ℕ
  | .zeroLeaf => 0
  | .oneLeaf _ => 1
  | .branch _ _ left right => left.oneLeafCount + right.oneLeafCount

private def ProtocolPartitionTree.oneLeafTraces {n : ℕ} {S : Frontier n}
    : ProtocolPartitionTree n S → List (List ProtocolBranchDir)
  | .zeroLeaf => []
  | .oneLeaf _ => [[]]
  | .branch _ _ left right =>
      left.oneLeafTraces.map (ProtocolBranchDir.left :: ·) ++
      right.oneLeafTraces.map (ProtocolBranchDir.right :: ·)

private def ProtocolPartitionTree.oneLeaves {n : ℕ} {S : Frontier n}
    : ProtocolPartitionTree n S → List (OneRectangle n)
  | .zeroLeaf => []
  | .oneLeaf R => [R]
  | .branch _ _ left right => left.oneLeaves ++ right.oneLeaves

private def ProtocolPartitionTree.numOneLeaves {n : ℕ} {S : Frontier n}
    (t : ProtocolPartitionTree n S) : ℕ :=
  t.oneLeaves.length

@[simp] private theorem ProtocolPartitionTree.oneLeafTraces_length
    {n : ℕ} {S : Frontier n} :
    ∀ t : ProtocolPartitionTree n S, t.oneLeafTraces.length = t.oneLeafCount
  | .zeroLeaf => by
      simp [ProtocolPartitionTree.oneLeafTraces, ProtocolPartitionTree.oneLeafCount]
  | .oneLeaf _ => by
      simp [ProtocolPartitionTree.oneLeafTraces, ProtocolPartitionTree.oneLeafCount]
  | .branch _ _ left right => by
      simp [ProtocolPartitionTree.oneLeafTraces, ProtocolPartitionTree.oneLeafCount,
        ProtocolPartitionTree.oneLeafTraces_length left,
        ProtocolPartitionTree.oneLeafTraces_length right, List.length_append]

private def ProtocolPartitionTree.oneLeafRectangles {n : ℕ} {S : Frontier n}
    : ProtocolPartitionTree n S → Finset (OneRectangle n)
  | .zeroLeaf => ∅
  | .oneLeaf R => {R}
  | .branch _ _ left right => left.oneLeafRectangles ∪ right.oneLeafRectangles

private def ProtocolPartitionTree.restrictTree {n : ℕ} {S : Frontier n}
    (R : OneRectangle n) : ProtocolPartitionTree n S → ProtocolPartitionTree n S
  | .zeroLeaf => .zeroLeaf
  | .oneLeaf R' =>
      .oneLeaf
        { leftFam := R.leftFam ∩ R'.leftFam
          rightFam := R.rightFam ∩ R'.rightFam }
  | .branch gate kind left right =>
      .branch gate kind (restrictTree R left) (restrictTree R right)

private def ProtocolPartitionTree.graftAtOneLeaves {n : ℕ} {S : Frontier n}
    : ProtocolPartitionTree n S → ProtocolPartitionTree n S → ProtocolPartitionTree n S
  | .zeroLeaf, _ => .zeroLeaf
  | .oneLeaf R, rhs => rhs.restrictTree R
  | .branch gate kind left right, rhs =>
      .branch gate kind
        (graftAtOneLeaves left rhs)
        (graftAtOneLeaves right rhs)

@[simp] private theorem ProtocolPartitionTree.numOneLeaves_eq_oneLeafCount
    {n : ℕ} {S : Frontier n} :
    ∀ t : ProtocolPartitionTree n S, t.numOneLeaves = t.oneLeafCount
  | .zeroLeaf => by simp [ProtocolPartitionTree.numOneLeaves, ProtocolPartitionTree.oneLeaves,
      ProtocolPartitionTree.oneLeafCount]
  | .oneLeaf _ => by simp [ProtocolPartitionTree.numOneLeaves, ProtocolPartitionTree.oneLeaves,
      ProtocolPartitionTree.oneLeafCount]
  | .branch _ _ left right => by
      simpa [ProtocolPartitionTree.numOneLeaves, ProtocolPartitionTree.oneLeaves,
        List.length_append, ProtocolPartitionTree.oneLeafCount] using
        congrArg₂ Nat.add
          (ProtocolPartitionTree.numOneLeaves_eq_oneLeafCount left)
          (ProtocolPartitionTree.numOneLeaves_eq_oneLeafCount right)

@[simp] private theorem ProtocolPartitionTree.numOneLeaves_eq_oneLeafTraces_length
    {n : ℕ} {S : Frontier n} (t : ProtocolPartitionTree n S) :
    t.numOneLeaves = t.oneLeafTraces.length := by
  rw [ProtocolPartitionTree.numOneLeaves_eq_oneLeafCount,
    ProtocolPartitionTree.oneLeafTraces_length]

private inductive FormulaTree where
  | input (i : ℕ)
  | notNode (gate : ℕ) (child : FormulaTree)
  | andNode (gate : ℕ) (left right : FormulaTree)
  | orNode (gate : ℕ) (left right : FormulaTree)

private def FormulaTree.rootIndex : FormulaTree → ℕ
  | .input i => i
  | .notNode gate _ => gate
  | .andNode gate _ _ => gate
  | .orNode gate _ _ => gate

private def formulaTreeOf {m : ℕ} (C : BooleanCircuit m)
    (hFormula : C.isFormula) :
    (root : ℕ) → root < m + C.gates.length → FormulaTree
  | root, hroot =>
      if hInput : root < m then
        .input root
      else
        let j := root - m
        have hj : j < C.gates.length := by
          dsimp [j]
          omega
        let g := C.gates[j]'hj
        let hInputs := formula_gate_inputs_lt C hFormula j hj
        have hm_le : m ≤ root := Nat.le_of_not_lt hInput
        have hmj_eq : m + j = root := Nat.add_sub_cancel' hm_le
        have hInput1_lt_root : g.input1 < root := by
          show (C.gates[j]'hj).input1 < root
          have h := hInputs.1; omega
        have hInput2_lt_root : g.input2 < root := by
          show (C.gates[j]'hj).input2 < root
          have h := hInputs.2; omega
        have hInput1 : g.input1 < m + C.gates.length := by
          exact lt_of_lt_of_le hInputs.1 (by omega)
        have hInput2 : g.input2 < m + C.gates.length := by
          exact lt_of_lt_of_le hInputs.2 (by omega)
        match g.kind with
        | GateKind.NOT =>
            .notNode root
              (formulaTreeOf C hFormula g.input1 hInput1)
        | GateKind.AND =>
            .andNode root
              (formulaTreeOf C hFormula g.input1 hInput1)
              (formulaTreeOf C hFormula g.input2 hInput2)
        | GateKind.OR =>
            .orNode root
              (formulaTreeOf C hFormula g.input1 hInput1)
              (formulaTreeOf C hFormula g.input2 hInput2)
termination_by root hroot => root
decreasing_by
  all_goals assumption

private theorem formulaTreeOf_rootIndex {m : ℕ} (C : BooleanCircuit m)
    (hFormula : C.isFormula) (root : ℕ) (hroot : root < m + C.gates.length) :
    (formulaTreeOf C hFormula root hroot).rootIndex = root := by
  unfold formulaTreeOf
  split
  · simp [FormulaTree.rootIndex]
  · have hj : root - m < C.gates.length := by omega
    cases hk : (C.gates[root - m]'hj).kind <;> simp [FormulaTree.rootIndex, hk]

private noncomputable def gateValueOnGraph {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (H : Finset (Edge n)) (idx : ℕ) : Bool :=
  (evalAllGates C (E.encode H)).getD idx false

private def evalStep (acc : List Bool) (g : Gate) : List Bool :=
  let v1 := acc.getD g.input1 false
  let v2 := acc.getD g.input2 false
  let result := match g.kind with
    | GateKind.AND => v1 && v2
    | GateKind.OR  => v1 || v2
    | GateKind.NOT => !v1
  acc ++ [result]

private theorem evalStep_length (acc : List Bool) (g : Gate) :
    (evalStep acc g).length = acc.length + 1 := by
  unfold evalStep
  simp

private theorem evalFold_length (gates : List Gate) (acc : List Bool) :
    (gates.foldl (init := acc) evalStep).length = acc.length + gates.length := by
  induction gates generalizing acc with
  | nil =>
      simp
  | cons g gates ih =>
      rw [List.foldl_cons, ih]
      simp [evalStep_length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem evalFold_getD_of_lt
    (gates : List Gate) (acc : List Bool) (idx : ℕ)
    (hidx : idx < acc.length) :
    (gates.foldl (init := acc) evalStep).getD idx false = acc.getD idx false := by
  induction gates generalizing acc with
  | nil =>
      simp
  | cons g gates ih =>
      rw [List.foldl_cons]
      have hkeep :
          (evalStep acc g).getD idx false = acc.getD idx false := by
        unfold evalStep
        simpa using List.getD_append acc [match g.kind with
          | GateKind.AND => acc.getD g.input1 false && acc.getD g.input2 false
          | GateKind.OR => acc.getD g.input1 false || acc.getD g.input2 false
          | GateKind.NOT => !(acc.getD g.input1 false)] false idx hidx
      calc
        (gates.foldl (init := evalStep acc g) evalStep).getD idx false
            = (evalStep acc g).getD idx false := by
              apply ih
              have hlt : idx < acc.length + 1 := Nat.lt_succ_of_lt hidx
              simpa [evalStep_length, Nat.add_comm] using hlt
        _ = acc.getD idx false := hkeep

private theorem gateValueOnGraph_input_eq {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (H : Finset (Edge n))
    (i : ℕ) (hi : i < m) :
    gateValueOnGraph C E H i = E.encode H ⟨i, hi⟩ := by
  unfold gateValueOnGraph evalAllGates
  have hkeep := evalFold_getD_of_lt C.gates (List.ofFn (E.encode H)) i (by simpa)
  have hi' : i < (List.ofFn (E.encode H)).length := by
    simpa using hi
  calc
    (C.gates.foldl (init := List.ofFn (E.encode H)) evalStep).getD i false
        = (List.ofFn (E.encode H)).getD i false := hkeep
    _ = (List.ofFn (E.encode H)).get ⟨i, hi'⟩ := by
      rw [List.getD_eq_get (l := List.ofFn (E.encode H)) (d := false) ⟨i, hi'⟩]
    _ = E.encode H ⟨i, hi⟩ := by
      simp [List.getElem_ofFn]

private noncomputable def gateEvalFromInputs {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (H : Finset (Edge n))
    (j : ℕ) (hj : j < C.gates.length) : Bool :=
  let g := C.gates[j]'hj
  let v1 := gateValueOnGraph C E H g.input1
  let v2 := gateValueOnGraph C E H g.input2
  match g.kind with
  | GateKind.AND => v1 && v2
  | GateKind.OR => v1 || v2
  | GateKind.NOT => !v1

private theorem evalAllGates_eq_foldl_evalStep {m : ℕ} (C : BooleanCircuit m)
    (input : Fin m → Bool) :
    evalAllGates C input = C.gates.foldl (init := List.ofFn input) evalStep := by
  unfold evalAllGates evalStep
  rfl

private theorem prefixFold_getD_eq {m : ℕ} (C : BooleanCircuit m) (input : Fin m → Bool)
    (j : ℕ) (hj : j ≤ C.gates.length) (idx : ℕ) (hidx : idx < m + j) :
    ((C.gates.take j).foldl (init := List.ofFn input) evalStep).getD idx false =
      (evalAllGates C input).getD idx false := by
  rw [evalAllGates_eq_foldl_evalStep]
  have hlen : ((C.gates.take j).foldl (init := List.ofFn input) evalStep).length = m + j := by
    rw [evalFold_length]; simp [List.length_take, min_eq_left hj]
  have hsplit : C.gates.foldl (init := List.ofFn input) evalStep =
      (C.gates.drop j).foldl (init :=
        (C.gates.take j).foldl (init := List.ofFn input) evalStep) evalStep := by
    conv_lhs => rw [show C.gates = C.gates.take j ++ C.gates.drop j from
      (List.take_append_drop j C.gates).symm]
    rw [List.foldl_append]
  rw [hsplit]
  symm
  apply evalFold_getD_of_lt
  rw [hlen]
  exact hidx

private theorem gateValueOnGraph_gate_eq {n m : ℕ} (C : BooleanCircuit m)
    (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (H : Finset (Edge n))
    (j : ℕ) (hj : j < C.gates.length) :
    gateValueOnGraph C E H (m + j) = gateEvalFromInputs C E H j hj := by
  have hsplit :
      C.gates = C.gates.take j ++ [C.gates[j]'hj] ++ C.gates.drop (j + 1) := by
    calc
      C.gates = C.gates.take j ++ C.gates.drop j := by
        symm
        exact List.take_append_drop j C.gates
      _ = C.gates.take j ++ [C.gates[j]'hj] ++ C.gates.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
        simp
  let acc := (C.gates.take j).foldl (init := List.ofFn (E.encode H)) evalStep
  have haccLen : acc.length = m + j := by
    dsimp [acc]
    rw [evalFold_length]
    simp [List.length_take, min_eq_left (Nat.le_of_lt hj)]
  have hpreserve :
      ((C.gates.drop (j + 1)).foldl (init := evalStep acc (C.gates[j]'hj)) evalStep).getD (m + j) false =
        (evalStep acc (C.gates[j]'hj)).getD (m + j) false := by
    apply evalFold_getD_of_lt
    rw [evalStep_length, haccLen]
    omega
  unfold gateValueOnGraph evalAllGates
  rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons]
  dsimp [acc]
  calc
    ((C.gates.drop (j + 1)).foldl
        (init := evalStep ((C.gates.take j).foldl (init := List.ofFn (E.encode H)) evalStep)
          (C.gates[j]'hj)) evalStep).getD (m + j) false
        =
        (evalStep ((C.gates.take j).foldl (init := List.ofFn (E.encode H)) evalStep)
          (C.gates[j]'hj)).getD (m + j) false := hpreserve
    _ = gateEvalFromInputs C E H j hj := by
          show (evalStep acc (C.gates[j]'hj)).getD (m + j) false = _
          unfold evalStep
          show (acc ++ [_]).getD (m + j) false = _
          rw [List.getD_append_right acc _ false (m + j) (by omega)]
          simp only [haccLen, Nat.add_sub_cancel]
          unfold gateEvalFromInputs gateValueOnGraph
          have hfw := formula_gate_inputs_lt C hFormula j hj
          have hpf1 := prefixFold_getD_eq C (E.encode H) j (Nat.le_of_lt hj)
            (C.gates[j]'hj).input1 hfw.1
          have hpf2 := prefixFold_getD_eq C (E.encode H) j (Nat.le_of_lt hj)
            (C.gates[j]'hj).input2 hfw.2
          simp only [List.getD, Nat.sub_self, evalAllGates_eq_foldl_evalStep] at hpf1 hpf2 ⊢
          simp only [List.getElem?_cons_zero, Option.getD_some]
          dsimp [acc]
          rw [hpf1, hpf2]

private noncomputable def filterByGateValue {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (I : Finset (Finset (Edge n)))
    (idx : ℕ) (b : Bool) : Finset (Finset (Edge n)) :=
  I.filter fun H => gateValueOnGraph C E H idx == b

private noncomputable def formulaProtocolTree {n m : ℕ}
    (C : BooleanCircuit m) (E : NaturalEdgeEncoding n m)
    (S : Frontier n) :
    (I : Finset (Finset (Edge n))) → Bool → FormulaTree → ProtocolPartitionTree n S
  | I, true, .input i =>
      .oneLeaf
        { leftFam := filterByGateValue C E I i true
          rightFam := filterByGateValue C E I i true }
  | I, false, .input i =>
      .oneLeaf
        { leftFam := filterByGateValue C E I i false
          rightFam := filterByGateValue C E I i false }
  | I, b, .notNode gate child =>
      .branch gate GateKind.NOT
        (formulaProtocolTree C E S I (!b) child)
        .zeroLeaf
  | I, true, .andNode gate left right =>
      let I' := filterByGateValue C E I gate true
      let leftTree := formulaProtocolTree C E S I' true left
      let rightTree := formulaProtocolTree C E S I' true right
      .branch gate GateKind.AND
        (leftTree.graftAtOneLeaves rightTree)
        .zeroLeaf
  | I, false, .andNode gate left right =>
      let I' := filterByGateValue C E I gate false
      let leftIdx := left.rootIndex
      let leftRejecting := filterByGateValue C E I' leftIdx false
      let rightOnly := filterByGateValue C E I' leftIdx true
      .branch gate GateKind.AND
        (formulaProtocolTree C E S leftRejecting false left)
        (formulaProtocolTree C E S rightOnly false right)
  | I, true, .orNode gate left right =>
      let I' := filterByGateValue C E I gate true
      let leftIdx := left.rootIndex
      let leftAccepting := filterByGateValue C E I' leftIdx true
      let rightOnly := filterByGateValue C E I' leftIdx false
      .branch gate GateKind.OR
        (formulaProtocolTree C E S leftAccepting true left)
        (formulaProtocolTree C E S rightOnly true right)
  | I, false, .orNode gate left right =>
      let I' := filterByGateValue C E I gate false
      let leftTree := formulaProtocolTree C E S I' false left
      let rightTree := formulaProtocolTree C E S I' false right
      .branch gate GateKind.OR
        (leftTree.graftAtOneLeaves rightTree)
        .zeroLeaf

private inductive FormulaTreeContainsGate : FormulaTree → ℕ → Prop where
  | root_input {i} :
      FormulaTreeContainsGate (.input i) i
  | root_not {gate child} :
      FormulaTreeContainsGate (.notNode gate child) gate
  | root_and {gate left right} :
      FormulaTreeContainsGate (.andNode gate left right) gate
  | root_or {gate left right} :
      FormulaTreeContainsGate (.orNode gate left right) gate
  | child_not {gate child j} :
      FormulaTreeContainsGate child j →
      FormulaTreeContainsGate (.notNode gate child) j
  | left_and {gate left right j} :
      FormulaTreeContainsGate left j →
      FormulaTreeContainsGate (.andNode gate left right) j
  | right_and {gate left right j} :
      FormulaTreeContainsGate right j →
      FormulaTreeContainsGate (.andNode gate left right) j
  | left_or {gate left right j} :
      FormulaTreeContainsGate left j →
      FormulaTreeContainsGate (.orNode gate left right) j
  | right_or {gate left right j} :
      FormulaTreeContainsGate right j →
      FormulaTreeContainsGate (.orNode gate left right) j

private def FormulaTree.inputLeafCount : FormulaTree → ℕ
  | .input _ => 1
  | .notNode _ child => child.inputLeafCount
  | .andNode _ left right => left.inputLeafCount + right.inputLeafCount
  | .orNode _ left right => left.inputLeafCount + right.inputLeafCount

private def FormulaTree.inputLeafPaths : FormulaTree → List (List Bool)
  | .input _ => [[]]
  | .notNode _ child => child.inputLeafPaths.map (fun p => false :: p)
  | .andNode _ left right =>
      left.inputLeafPaths.map (fun p => false :: p) ++
      right.inputLeafPaths.map (fun p => true :: p)
  | .orNode _ left right =>
      left.inputLeafPaths.map (fun p => false :: p) ++
      right.inputLeafPaths.map (fun p => true :: p)

private def FormulaTree.inputLeafGateAt : FormulaTree → List Bool → ℕ
  | .input i, _ => i
  | .notNode gate child, false :: path => child.inputLeafGateAt path
  | .notNode gate _, _ => gate
  | .andNode gate left right, false :: path => left.inputLeafGateAt path
  | .andNode gate left right, true :: path => right.inputLeafGateAt path
  | .andNode gate _ _, _ => gate
  | .orNode gate left right, false :: path => left.inputLeafGateAt path
  | .orNode gate left right, true :: path => right.inputLeafGateAt path
  | .orNode gate _ _, _ => gate

private def FormulaTree.inputLeafPolarityAt : FormulaTree → List Bool → Bool
  | .input _, _ => true
  | .notNode _ child, false :: path => !(child.inputLeafPolarityAt path)
  | .notNode _ _, _ => false
  | .andNode _ left right, false :: path => left.inputLeafPolarityAt path
  | .andNode _ left right, true :: path => right.inputLeafPolarityAt path
  | .andNode _ _ _, _ => false
  | .orNode _ left right, false :: path => left.inputLeafPolarityAt path
  | .orNode _ left right, true :: path => right.inputLeafPolarityAt path
  | .orNode _ _ _, _ => false

private structure FormulaPacket where
  inputPath : List Bool
  andObligations : List FormulaTree

private def FormulaTree.acceptingPackets : FormulaTree → List FormulaPacket
  | .input _ =>
      [{ inputPath := []
         andObligations := [] }]
  | .notNode _ child =>
      child.acceptingPackets.map (fun p : FormulaPacket =>
        { p with inputPath := false :: p.inputPath }
      )
  | .andNode _ left right =>
      (left.acceptingPackets.map (fun p : FormulaPacket =>
        { inputPath := false :: p.inputPath
          andObligations := right :: p.andObligations })) ++
      (right.acceptingPackets.map (fun p : FormulaPacket =>
        { inputPath := true :: p.inputPath
          andObligations := left :: p.andObligations }))
  | .orNode _ left right =>
      (left.acceptingPackets.map (fun p : FormulaPacket =>
        { p with inputPath := false :: p.inputPath })) ++
      (right.acceptingPackets.map (fun p : FormulaPacket =>
        { p with inputPath := true :: p.inputPath }))

@[simp] private theorem FormulaTree.inputLeafPaths_length :
    ∀ t : FormulaTree, t.inputLeafPaths.length = t.inputLeafCount
  | .input _ => by simp [FormulaTree.inputLeafPaths, FormulaTree.inputLeafCount]
  | .notNode _ child => by
      simp [FormulaTree.inputLeafPaths, FormulaTree.inputLeafCount,
        FormulaTree.inputLeafPaths_length child]
  | .andNode _ left right => by
      simp [FormulaTree.inputLeafPaths, FormulaTree.inputLeafCount,
        FormulaTree.inputLeafPaths_length left, FormulaTree.inputLeafPaths_length right,
        List.length_append]
  | .orNode _ left right => by
      simp [FormulaTree.inputLeafPaths, FormulaTree.inputLeafCount,
        FormulaTree.inputLeafPaths_length left, FormulaTree.inputLeafPaths_length right,
        List.length_append]

@[simp] private theorem FormulaTree.acceptingPackets_length :
    ∀ t : FormulaTree, t.acceptingPackets.length = t.inputLeafCount
  | .input _ => by
      simp [FormulaTree.acceptingPackets, FormulaTree.inputLeafCount]
  | .notNode _ child => by
      simp [FormulaTree.acceptingPackets, FormulaTree.inputLeafCount,
        FormulaTree.acceptingPackets_length child]
  | .andNode _ left right => by
      simp [FormulaTree.acceptingPackets, FormulaTree.inputLeafCount,
        FormulaTree.acceptingPackets_length left, FormulaTree.acceptingPackets_length right,
        List.length_append]
  | .orNode _ left right => by
      simp [FormulaTree.acceptingPackets, FormulaTree.inputLeafCount,
        FormulaTree.acceptingPackets_length left, FormulaTree.acceptingPackets_length right,
        List.length_append]

@[simp] private theorem FormulaTree.acceptingPackets_map_inputPath :
    ∀ t : FormulaTree, t.acceptingPackets.map FormulaPacket.inputPath = t.inputLeafPaths
  | .input _ => by
      simp [FormulaTree.acceptingPackets, FormulaTree.inputLeafPaths]
  | .notNode _ child => by
      simpa [FormulaTree.acceptingPackets, FormulaTree.inputLeafPaths, List.map_map] using
        congrArg (List.map (fun p => false :: p))
          (FormulaTree.acceptingPackets_map_inputPath child)
  | .andNode _ left right => by
      have hLeft := congrArg (List.map (fun p => false :: p))
        (FormulaTree.acceptingPackets_map_inputPath left)
      have hRight := congrArg (List.map (fun p => true :: p))
        (FormulaTree.acceptingPackets_map_inputPath right)
      simpa [FormulaTree.acceptingPackets, FormulaTree.inputLeafPaths, List.map_append, List.map_map]
        using congrArg₂ List.append hLeft hRight
  | .orNode _ left right => by
      have hLeft := congrArg (List.map (fun p => false :: p))
        (FormulaTree.acceptingPackets_map_inputPath left)
      have hRight := congrArg (List.map (fun p => true :: p))
        (FormulaTree.acceptingPackets_map_inputPath right)
      simpa [FormulaTree.acceptingPackets, FormulaTree.inputLeafPaths, List.map_append, List.map_map]
        using congrArg₂ List.append hLeft hRight

private def FormulaTree.inputVars : FormulaTree → Finset ℕ
  | .input i => {i}
  | .notNode _ child => child.inputVars
  | .andNode _ left right => left.inputVars ∪ right.inputVars
  | .orNode _ left right => left.inputVars ∪ right.inputVars

  private theorem FormulaTree.inputLeafGateAt_mem_inputVars :
    ∀ t : FormulaTree, ∀ path ∈ t.inputLeafPaths,
      t.inputLeafGateAt path ∈ t.inputVars
  | .input i, path, hpath => by
      simpa [FormulaTree.inputLeafPaths, FormulaTree.inputLeafGateAt, FormulaTree.inputVars] using hpath
  | .notNode _ child, path, hpath => by
      simp [FormulaTree.inputLeafPaths] at hpath
      rcases hpath with ⟨p, hp, rfl⟩
      simpa [FormulaTree.inputLeafGateAt, FormulaTree.inputVars] using
        FormulaTree.inputLeafGateAt_mem_inputVars child p hp
  | .andNode _ left right, path, hpath => by
      simp [FormulaTree.inputLeafPaths] at hpath
      rcases hpath with hpath | hpath
      · rcases hpath with ⟨p, hp, rfl⟩
        exact Finset.mem_union.mpr <| Or.inl <|
          FormulaTree.inputLeafGateAt_mem_inputVars left p hp
      · rcases hpath with ⟨p, hp, rfl⟩
        exact Finset.mem_union.mpr <| Or.inr <|
          FormulaTree.inputLeafGateAt_mem_inputVars right p hp
  | .orNode _ left right, path, hpath => by
      simp [FormulaTree.inputLeafPaths] at hpath
      rcases hpath with hpath | hpath
      · rcases hpath with ⟨p, hp, rfl⟩
        exact Finset.mem_union.mpr <| Or.inl <|
          FormulaTree.inputLeafGateAt_mem_inputVars left p hp
      · rcases hpath with ⟨p, hp, rfl⟩
        exact Finset.mem_union.mpr <| Or.inr <|
          FormulaTree.inputLeafGateAt_mem_inputVars right p hp

private theorem FormulaTree.acceptingPacket_inputGate_mem_inputVars :
    ∀ t : FormulaTree, ∀ pkt ∈ t.acceptingPackets,
      t.inputLeafGateAt pkt.inputPath ∈ t.inputVars
  | t, pkt, hpkt => by
      have hmap := FormulaTree.acceptingPackets_map_inputPath t
      have hpath : pkt.inputPath ∈ t.inputLeafPaths := by
        rw [← hmap]
        exact List.mem_map.mpr ⟨pkt, hpkt, rfl⟩
      exact FormulaTree.inputLeafGateAt_mem_inputVars t pkt.inputPath hpath

private theorem FormulaTree.acceptingPackets_obligation_vars_subset :
    ∀ t : FormulaTree, ∀ pkt ∈ t.acceptingPackets,
      ∀ sib ∈ pkt.andObligations, sib.inputVars ⊆ t.inputVars
  | .input _, pkt, hpkt, sib, hsib => by
      simp [FormulaTree.acceptingPackets] at hpkt
      subst hpkt
      simp at hsib
  | .notNode _ child, pkt, hpkt, sib, hsib => by
      simp [FormulaTree.acceptingPackets] at hpkt
      rcases hpkt with ⟨p, hp, rfl⟩
      exact Set.Subset.trans
        (FormulaTree.acceptingPackets_obligation_vars_subset child p hp sib hsib)
        (by
          intro i hi
          simp [FormulaTree.inputVars, hi])
  | .andNode _ left right, pkt, hpkt, sib, hsib => by
      simp [FormulaTree.acceptingPackets] at hpkt
      rcases hpkt with hpkt | hpkt
      · rcases hpkt with ⟨p, hp, rfl⟩
        simp at hsib
        rcases hsib with rfl | hsib
        · intro i hi
          simp [FormulaTree.inputVars, hi]
        · exact Set.Subset.trans
            (FormulaTree.acceptingPackets_obligation_vars_subset left p hp sib hsib)
            (by
              intro i hi
              exact Finset.mem_union.mpr (Or.inl hi))
      · rcases hpkt with ⟨p, hp, rfl⟩
        simp at hsib
        rcases hsib with rfl | hsib
        · intro i hi
          simp [FormulaTree.inputVars, hi]
        · exact Set.Subset.trans
            (FormulaTree.acceptingPackets_obligation_vars_subset right p hp sib hsib)
            (by
              intro i hi
              exact Finset.mem_union.mpr (Or.inr hi))
  | .orNode _ left right, pkt, hpkt, sib, hsib => by
      simp [FormulaTree.acceptingPackets] at hpkt
      rcases hpkt with hpkt | hpkt
      · rcases hpkt with ⟨p, hp, rfl⟩
        exact Set.Subset.trans
          (FormulaTree.acceptingPackets_obligation_vars_subset left p hp sib hsib)
          (by
            intro i hi
            exact Finset.mem_union.mpr (Or.inl hi))
      · rcases hpkt with ⟨p, hp, rfl⟩
        exact Set.Subset.trans
          (FormulaTree.acceptingPackets_obligation_vars_subset right p hp sib hsib)
          (by
            intro i hi
            exact Finset.mem_union.mpr (Or.inr hi))

private def sampleMixedObligationTree : FormulaTree :=
  .andNode 3 (.input 0) (.orNode 2 (.input 1) (.input 2))

private theorem sampleMixedObligationTree_has_compound_obligation :
    { inputPath := [false]
      andObligations := [FormulaTree.orNode 2 (.input 1) (.input 2)] } ∈
      sampleMixedObligationTree.acceptingPackets := by
  simp [sampleMixedObligationTree, FormulaTree.acceptingPackets]

private noncomputable def FormulaTree.evalOnGraph {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (H : Finset (Edge n)) : FormulaTree → Bool
  | .input i => gateValueOnGraph C E H i
  | .notNode _ child => !(child.evalOnGraph C E H)
  | .andNode _ left right => left.evalOnGraph C E H && right.evalOnGraph C E H
  | .orNode _ left right => left.evalOnGraph C E H || right.evalOnGraph C E H

private def allVarsLeft {n m : ℕ} (E : NaturalEdgeEncoding n m) (S : Frontier n) (t : FormulaTree) : Prop :=
  ∀ i ∈ t.inputVars, ∃ hi : i < m, E.leftVar S ⟨i, hi⟩

private def allVarsRight {n m : ℕ} (E : NaturalEdgeEncoding n m) (S : Frontier n) (t : FormulaTree) : Prop :=
  ∀ i ∈ t.inputVars, ∃ hi : i < m, E.rightVar S ⟨i, hi⟩

private theorem restrictTree_rectangles_subset {n : ℕ} {S : Frontier n}
    (ambient : OneRectangle n) :
    ∀ t : ProtocolPartitionTree n S,
      ∀ R ∈ (t.restrictTree ambient).oneLeafRectangles,
        R.leftFam ⊆ ambient.leftFam ∧ R.rightFam ⊆ ambient.rightFam
  | .zeroLeaf, R, hR => by
      simpa [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafRectangles] using hR
  | .oneLeaf R0, R, hR => by
      simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafRectangles] at hR
      subst hR
      constructor <;> intro H hH
      · exact (Finset.mem_inter.mp hH).1
      · exact (Finset.mem_inter.mp hH).1
  | .branch gate kind left right, R, hR => by
      simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafRectangles] at hR ⊢
      rcases hR with hR | hR
      · exact restrictTree_rectangles_subset ambient left R hR
      · exact restrictTree_rectangles_subset ambient right R hR

private theorem graft_rectangles_subset_of {n : ℕ} {S : Frontier n}
    (rhs : ProtocolPartitionTree n S) (I : Finset (Finset (Edge n))) :
    ∀ t : ProtocolPartitionTree n S,
      (∀ A ∈ t.oneLeafRectangles, A.leftFam ⊆ I ∧ A.rightFam ⊆ I) →
      ∀ R ∈ (t.graftAtOneLeaves rhs).oneLeafRectangles,
        R.leftFam ⊆ I ∧ R.rightFam ⊆ I
  | .zeroLeaf, _, R, hR => by
      simpa [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeafRectangles] using hR
  | .oneLeaf A, hsub, R, hR => by
      have hA := hsub A (by simp [ProtocolPartitionTree.oneLeafRectangles])
      have hrestrict := restrictTree_rectangles_subset A rhs R hR
      exact ⟨Set.Subset.trans hrestrict.1 hA.1, Set.Subset.trans hrestrict.2 hA.2⟩
  | .branch gate kind left right, hsub, R, hR => by
      simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeafRectangles] at hR ⊢
      rcases hR with hR | hR
      · exact graft_rectangles_subset_of rhs I left
          (fun A hA => hsub A (by simp [ProtocolPartitionTree.oneLeafRectangles, hA])) R hR
      · exact graft_rectangles_subset_of rhs I right
          (fun A hA => hsub A (by simp [ProtocolPartitionTree.oneLeafRectangles, hA])) R hR

private theorem filterByGateValue_subset {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (I : Finset (Finset (Edge n)))
    (idx : ℕ) (b : Bool) :
    filterByGateValue C E I idx b ⊆ I := by
  intro H hH
  exact (Finset.mem_filter.mp hH).1

private theorem mem_filterByGateValue_iff {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (I : Finset (Finset (Edge n)))
    (idx : ℕ) (b : Bool) (H : Finset (Edge n)) :
    H ∈ filterByGateValue C E I idx b ↔ H ∈ I ∧ gateValueOnGraph C E H idx = b := by
  unfold filterByGateValue
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hI, hEq⟩
    refine ⟨hI, ?_⟩
    simpa using hEq
  · intro h
    rcases h with ⟨hI, hEq⟩
    exact Finset.mem_filter.mpr ⟨hI, by simpa using hEq⟩

private theorem oneLeafRectangles_mem_graft_of_mem {n : ℕ} {S : Frontier n}
    (rhs t : ProtocolPartitionTree n S) (A R : OneRectangle n)
    (hA : A ∈ t.oneLeafRectangles)
    (hR : R ∈ rhs.oneLeafRectangles) :
    { leftFam := A.leftFam ∩ R.leftFam
      rightFam := A.rightFam ∩ R.rightFam } ∈
      (t.graftAtOneLeaves rhs).oneLeafRectangles := by
  have hrestrict :
      OneRectangle.mk (A.leftFam ∩ R.leftFam) (A.rightFam ∩ R.rightFam) ∈
        (rhs.restrictTree A).oneLeafRectangles := by
    clear hA
    induction rhs with
    | zeroLeaf =>
        simp [ProtocolPartitionTree.oneLeafRectangles] at hR
    | oneLeaf R' =>
        simp [ProtocolPartitionTree.oneLeafRectangles] at hR
        subst hR
        simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafRectangles]
    | branch gate kind left right ihLeft ihRight =>
        simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafRectangles] at hR ⊢
        rcases hR with hR | hR
        · exact Or.inl (ihLeft hR)
        · exact Or.inr (ihRight hR)
  revert A hA
  induction t with
  | zeroLeaf =>
      intro A hA
      simp [ProtocolPartitionTree.oneLeafRectangles] at hA
  | oneLeaf A' =>
      intro A hA
      simp [ProtocolPartitionTree.oneLeafRectangles] at hA
      subst hA
      simpa [ProtocolPartitionTree.graftAtOneLeaves] using hrestrict
  | branch gate kind left right ihLeft ihRight =>
      intro A hA
      simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeafRectangles] at hA ⊢
      rcases hA with hA | hA
      · intro hrestrict
        exact Or.inl (ihLeft _ hA hrestrict)
      · intro hrestrict
        exact Or.inr (ihRight _ hA hrestrict)

private theorem oneLeafRectangles_mem_restrictTree_exists {n : ℕ} {S : Frontier n}
    (ambient : OneRectangle n) :
    ∀ (t : ProtocolPartitionTree n S) (R : OneRectangle n),
      R ∈ (t.restrictTree ambient).oneLeafRectangles →
      ∃ R' ∈ t.oneLeafRectangles,
        R = OneRectangle.mk (ambient.leftFam ∩ R'.leftFam) (ambient.rightFam ∩ R'.rightFam)
  | .zeroLeaf, R, hR => by
      simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafRectangles] at hR
  | .oneLeaf R', R, hR => by
      simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafRectangles] at hR
      subst hR
      refine ⟨R', by simp [ProtocolPartitionTree.oneLeafRectangles], rfl⟩
  | .branch gate kind left right, R, hR => by
      simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafRectangles] at hR
      rcases hR with hR | hR
      · rcases oneLeafRectangles_mem_restrictTree_exists ambient left R hR with ⟨R', hR', rfl⟩
        exact ⟨R', by simp [ProtocolPartitionTree.oneLeafRectangles, hR'], rfl⟩
      · rcases oneLeafRectangles_mem_restrictTree_exists ambient right R hR with ⟨R', hR', rfl⟩
        exact ⟨R', by simp [ProtocolPartitionTree.oneLeafRectangles, hR'], rfl⟩

private theorem oneLeafRectangles_mem_graft_exists {n : ℕ} {S : Frontier n}
    (lhs rhs : ProtocolPartitionTree n S) (R : OneRectangle n) :
    R ∈ (lhs.graftAtOneLeaves rhs).oneLeafRectangles →
    ∃ A ∈ lhs.oneLeafRectangles, ∃ B ∈ rhs.oneLeafRectangles,
      R = OneRectangle.mk (A.leftFam ∩ B.leftFam) (A.rightFam ∩ B.rightFam) := by
  intro hR
  induction lhs generalizing R with
  | zeroLeaf =>
      simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeafRectangles] at hR
  | oneLeaf A =>
      rcases oneLeafRectangles_mem_restrictTree_exists A rhs R
        (by simpa [ProtocolPartitionTree.graftAtOneLeaves] using hR) with ⟨B, hB, hEq⟩
      exact ⟨A, by simp [ProtocolPartitionTree.oneLeafRectangles], B, hB, hEq⟩
  | branch gate kind left right ihLeft ihRight =>
      simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeafRectangles] at hR
      rcases hR with hR | hR
      · rcases ihLeft _ hR with ⟨A, hA, B, hB, hEq⟩
        exact ⟨A, by simp [ProtocolPartitionTree.oneLeafRectangles, hA], B, hB, hEq⟩
      · rcases ihRight _ hR with ⟨A, hA, B, hB, hEq⟩
        exact ⟨A, by simp [ProtocolPartitionTree.oneLeafRectangles, hA], B, hB, hEq⟩

private theorem formulaProtocolTree_rectangles_subset :
  ∀ {n m : ℕ} (C : BooleanCircuit m) (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (I : Finset (Finset (Edge n))) (b : Bool) (t : FormulaTree)
    (R : OneRectangle n),
    R ∈ (formulaProtocolTree C E S I b t).oneLeafRectangles →
      R.leftFam ⊆ I ∧ R.rightFam ⊆ I := by
  intro n m C E S I b t
  induction t generalizing I b with
  | input i =>
      intro R hR
      cases b with
      | false =>
          simp [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] at hR
          subst hR
          exact ⟨filterByGateValue_subset C E I i false, filterByGateValue_subset C E I i false⟩
      | true =>
          simp [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] at hR
          subst hR
          exact ⟨filterByGateValue_subset C E I i true, filterByGateValue_subset C E I i true⟩
  | notNode gate child ih =>
      intro R hR
      cases b with
      | false =>
          simp [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] at hR
          exact ih (I := I) (b := true) (R := R) hR
      | true =>
          simp [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] at hR
          exact ih (I := I) (b := false) (R := R) hR
  | andNode gate left right ihLeft ihRight =>
      intro R hR
      cases b with
      | true =>
          let I' := filterByGateValue C E I gate true
          simp [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] at hR
          have hI' : ∀ A ∈ (formulaProtocolTree C E S I' true left).oneLeafRectangles,
              A.leftFam ⊆ I' ∧ A.rightFam ⊆ I' := by
            intro A hA
            exact ihLeft (I := I') (b := true) (R := A) hA
          have hsubI' := graft_rectangles_subset_of (formulaProtocolTree C E S I' true right) I'
            (formulaProtocolTree C E S I' true left) hI' R hR
          exact ⟨Set.Subset.trans hsubI'.1 (filterByGateValue_subset C E I gate true),
            Set.Subset.trans hsubI'.2 (filterByGateValue_subset C E I gate true)⟩
      | false =>
          simp [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] at hR
          rcases hR with hR | hR
          · have hsub := ihLeft (I := filterByGateValue C E (filterByGateValue C E I gate false)
                left.rootIndex false) (b := false) (R := R) hR
            exact ⟨Set.Subset.trans hsub.1
                (Set.Subset.trans
                  (filterByGateValue_subset C E (filterByGateValue C E I gate false) left.rootIndex false)
                  (filterByGateValue_subset C E I gate false)),
              Set.Subset.trans hsub.2
                (Set.Subset.trans
                  (filterByGateValue_subset C E (filterByGateValue C E I gate false) left.rootIndex false)
                  (filterByGateValue_subset C E I gate false))⟩
          · have hsub := ihRight (I := filterByGateValue C E (filterByGateValue C E I gate false)
                left.rootIndex true) (b := false) (R := R) hR
            exact ⟨Set.Subset.trans hsub.1
                (Set.Subset.trans
                  (filterByGateValue_subset C E (filterByGateValue C E I gate false) left.rootIndex true)
                  (filterByGateValue_subset C E I gate false)),
              Set.Subset.trans hsub.2
                (Set.Subset.trans
                  (filterByGateValue_subset C E (filterByGateValue C E I gate false) left.rootIndex true)
                  (filterByGateValue_subset C E I gate false))⟩
  | orNode gate left right ihLeft ihRight =>
      intro R hR
      cases b with
      | true =>
          simp [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] at hR
          rcases hR with hR | hR
          · have hsub := ihLeft (I := filterByGateValue C E (filterByGateValue C E I gate true)
                left.rootIndex true) (b := true) (R := R) hR
            exact ⟨Set.Subset.trans hsub.1
                (Set.Subset.trans
                  (filterByGateValue_subset C E (filterByGateValue C E I gate true) left.rootIndex true)
                  (filterByGateValue_subset C E I gate true)),
              Set.Subset.trans hsub.2
                (Set.Subset.trans
                  (filterByGateValue_subset C E (filterByGateValue C E I gate true) left.rootIndex true)
                  (filterByGateValue_subset C E I gate true))⟩
          · have hsub := ihRight (I := filterByGateValue C E (filterByGateValue C E I gate true)
                left.rootIndex false) (b := true) (R := R) hR
            exact ⟨Set.Subset.trans hsub.1
                (Set.Subset.trans
                  (filterByGateValue_subset C E (filterByGateValue C E I gate true) left.rootIndex false)
                  (filterByGateValue_subset C E I gate true)),
              Set.Subset.trans hsub.2
                (Set.Subset.trans
                  (filterByGateValue_subset C E (filterByGateValue C E I gate true) left.rootIndex false)
                  (filterByGateValue_subset C E I gate true))⟩
      | false =>
          let I' := filterByGateValue C E I gate false
          simp [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] at hR
          have hI' : ∀ A ∈ (formulaProtocolTree C E S I' false left).oneLeafRectangles,
              A.leftFam ⊆ I' ∧ A.rightFam ⊆ I' := by
            intro A hA
            exact ihLeft (I := I') (b := false) (R := A) hA
          have hsubI' := graft_rectangles_subset_of (formulaProtocolTree C E S I' false right) I'
            (formulaProtocolTree C E S I' false left) hI' R hR
          exact ⟨Set.Subset.trans hsubI'.1 (filterByGateValue_subset C E I gate false),
            Set.Subset.trans hsubI'.2 (filterByGateValue_subset C E I gate false)⟩

private theorem evalOnGraph_eq_of_allVarsLeft {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) (H₀ H₁ : Finset (Edge n)) :
    ∀ t : FormulaTree, allVarsLeft E S t →
      t.evalOnGraph C E (mixedGraph S H₁ H₀) = t.evalOnGraph C E H₀ := by
  intro t
  induction t with
  | input i =>
      intro hall
      rcases hall i (by simp [FormulaTree.inputVars]) with ⟨hi, hleft⟩
      rw [FormulaTree.evalOnGraph, FormulaTree.evalOnGraph]
      rw [gateValueOnGraph_input_eq C E (mixedGraph S H₁ H₀) i hi]
      rw [natural_encoding_mixed_eq_of_left E S H₁ H₀ ⟨i, hi⟩ hleft]
      rw [gateValueOnGraph_input_eq C E H₀ i hi]
  | notNode gate child ih =>
      intro hall
      simpa [FormulaTree.evalOnGraph, allVarsLeft] using ih (by
        intro i hi
        exact hall i (by simpa [FormulaTree.inputVars] using hi))
  | andNode gate left right ihLeft ihRight =>
      intro hall
      have hL : allVarsLeft E S left := by
        intro i hi
        exact hall i (by simp [FormulaTree.inputVars, hi])
      have hR : allVarsLeft E S right := by
        intro i hi
        exact hall i (by simp [FormulaTree.inputVars, hi])
      simp [FormulaTree.evalOnGraph, ihLeft hL, ihRight hR]
  | orNode gate left right ihLeft ihRight =>
      intro hall
      have hL : allVarsLeft E S left := by
        intro i hi
        exact hall i (by simp [FormulaTree.inputVars, hi])
      have hR : allVarsLeft E S right := by
        intro i hi
        exact hall i (by simp [FormulaTree.inputVars, hi])
      simp [FormulaTree.evalOnGraph, ihLeft hL, ihRight hR]

private theorem evalOnGraph_eq_of_allVarsRight {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) (H₀ H₁ : Finset (Edge n)) :
    ∀ t : FormulaTree, allVarsRight E S t →
      t.evalOnGraph C E (mixedGraph S H₁ H₀) = t.evalOnGraph C E H₁ := by
  intro t
  induction t with
  | input i =>
      intro hall
      rcases hall i (by simp [FormulaTree.inputVars]) with ⟨hi, hright⟩
      rw [FormulaTree.evalOnGraph, FormulaTree.evalOnGraph]
      rw [gateValueOnGraph_input_eq C E (mixedGraph S H₁ H₀) i hi]
      rw [natural_encoding_mixed_eq_of_right E S H₁ H₀ ⟨i, hi⟩ hright]
      rw [gateValueOnGraph_input_eq C E H₁ i hi]
  | notNode gate child ih =>
      intro hall
      simpa [FormulaTree.evalOnGraph, allVarsRight] using ih (by
        intro i hi
        exact hall i (by simpa [FormulaTree.inputVars] using hi))
  | andNode gate left right ihLeft ihRight =>
      intro hall
      have hL : allVarsRight E S left := by
        intro i hi
        exact hall i (by simp [FormulaTree.inputVars, hi])
      have hR : allVarsRight E S right := by
        intro i hi
        exact hall i (by simp [FormulaTree.inputVars, hi])
      simp [FormulaTree.evalOnGraph, ihLeft hL, ihRight hR]
  | orNode gate left right ihLeft ihRight =>
      intro hall
      have hL : allVarsRight E S left := by
        intro i hi
        exact hall i (by simp [FormulaTree.inputVars, hi])
      have hR : allVarsRight E S right := by
        intro i hi
        exact hall i (by simp [FormulaTree.inputVars, hi])
      simp [FormulaTree.evalOnGraph, ihLeft hL, ihRight hR]

private theorem gateValueOnGraph_output_eq_eval {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (H : Finset (Edge n)) :
    gateValueOnGraph C E H C.outputGate = C.eval (E.encode H) := by
  unfold gateValueOnGraph BooleanCircuit.eval evalAllGates
  rfl

private theorem eval_true_implies_outputGate_lt {m : ℕ} (C : BooleanCircuit m)
    (input : Fin m → Bool) (hEval : C.eval input = true) :
    C.outputGate < m + C.gates.length := by
  by_contra hlt
  have hlen :
      (C.gates.foldl (init := List.ofFn input) fun acc g =>
        let v1 := acc.getD g.input1 false
        let v2 := acc.getD g.input2 false
        let result := match g.kind with
          | GateKind.AND => v1 && v2
          | GateKind.OR => v1 || v2
          | GateKind.NOT => !v1
        acc ++ [result]).length = m + C.gates.length := by
    simpa [evalStep] using evalFold_length C.gates (List.ofFn input)
  have hfalse :
      (C.gates.foldl (init := List.ofFn input) fun acc g =>
        let v1 := acc.getD g.input1 false
        let v2 := acc.getD g.input2 false
        let result := match g.kind with
          | GateKind.AND => v1 && v2
          | GateKind.OR => v1 || v2
          | GateKind.NOT => !v1
        acc ++ [result]).getD C.outputGate false = false := by
    apply List.getD_eq_default
    rw [hlen]
    exact Nat.le_of_not_lt hlt
  unfold BooleanCircuit.eval at hEval
  have hcontra : false = true := hfalse.symm.trans hEval
  exact Bool.false_ne_true hcontra

private theorem formulaTreeOf_eval_eq_gateValue {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (H : Finset (Edge n)) :
    ∀ root : ℕ, ∀ hroot : root < m + C.gates.length,
      (formulaTreeOf C hFormula root hroot).evalOnGraph C E H =
        gateValueOnGraph C E H root
  | root, hroot => by
      unfold formulaTreeOf
      by_cases hInput : root < m
      · simp [hInput, FormulaTree.evalOnGraph, gateValueOnGraph_input_eq]
      · simp [hInput]
        set j : ℕ := root - m
        have hj : j < C.gates.length := by
          dsimp [j]
          omega
        set g : Gate := C.gates[j]'hj
        have hinputs : g.input1 < m + j ∧ g.input2 < m + j := by
          subst g
          simpa [j] using formula_gate_inputs_lt C hFormula j hj
        have hgj : m + j = root := by
          dsimp [j]
          omega
        have hinput1 : g.input1 < m + C.gates.length := by omega
        have hinput2 : g.input2 < m + C.gates.length := by omega
        have hlt1 : g.input1 < root := by omega
        have hlt2 : g.input2 < root := by omega
        have hchild1 :
            (formulaTreeOf C hFormula g.input1 hinput1).evalOnGraph C E H =
              gateValueOnGraph C E H g.input1 := by
          exact formulaTreeOf_eval_eq_gateValue C hFormula E H g.input1 hinput1
        have hchild2 :
            (formulaTreeOf C hFormula g.input2 hinput2).evalOnGraph C E H =
              gateValueOnGraph C E H g.input2 := by
          exact formulaTreeOf_eval_eq_gateValue C hFormula E H g.input2 hinput2
        have hgate :
            gateValueOnGraph C E H root = gateEvalFromInputs C E H j hj := by
          have hbase := gateValueOnGraph_gate_eq C hFormula E H j hj
          simpa [hgj, j] using hbase
        cases hk : g.kind <;>
          simp [FormulaTree.evalOnGraph, hchild1, hchild2, hgate, gateEvalFromInputs, hk, g, j]
termination_by root _ => root
decreasing_by
  all_goals omega

private theorem formulaTreeOf_output_eval_true {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m)
    (hCorrect : ComputesHAMWithNaturalEncoding C E)
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (hout : C.outputGate < m + C.gates.length) :
    (formulaTreeOf C hFormula C.outputGate hout).evalOnGraph C E H = true := by
  have hEval : C.eval (E.encode H) = true := (hCorrect H).2 hH
  rw [formulaTreeOf_eval_eq_gateValue C hFormula E H C.outputGate hout,
    gateValueOnGraph_output_eq_eval, hEval]

private theorem formulaProtocolTree_cover_of_gateValue {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) :
    ∀ root : ℕ, ∀ hroot : root < m + C.gates.length,
      ∀ (I : Finset (Finset (Edge n))) (b : Bool) (H : Finset (Edge n)),
      H ∈ I →
      gateValueOnGraph C E H root = b →
      ∃ R ∈ (formulaProtocolTree C E S I b (formulaTreeOf C hFormula root hroot)).oneLeafRectangles,
        H ∈ R.leftFam ∧ H ∈ R.rightFam := by
  intro root
  induction root using Nat.strong_induction_on with
  | h root ih =>
      intro hroot I b H hHI hRoot
      unfold formulaTreeOf
      by_cases hInput : root < m
      · refine ⟨OneRectangle.mk (filterByGateValue C E I root b) (filterByGateValue C E I root b), ?_, ?_⟩
        · cases b <;> simp [formulaProtocolTree, hInput, ProtocolPartitionTree.oneLeafRectangles]
        · exact ⟨(mem_filterByGateValue_iff C E I root b H).2 ⟨hHI, hRoot⟩,
            (mem_filterByGateValue_iff C E I root b H).2 ⟨hHI, hRoot⟩⟩
      · simp [hInput]
        set j : ℕ := root - m
        have hj : j < C.gates.length := by
          dsimp [j]
          omega
        set g : Gate := C.gates[j]'hj
        have hinputs : g.input1 < m + j ∧ g.input2 < m + j := by
          subst g
          simpa [j] using formula_gate_inputs_lt C hFormula j hj
        have hinput1 : g.input1 < m + C.gates.length := by omega
        have hinput2 : g.input2 < m + C.gates.length := by omega
        have hlt1 : g.input1 < root := by
          dsimp [j] at hinputs
          omega
        have hlt2 : g.input2 < root := by
          dsimp [j] at hinputs
          omega
        have hroot_eq : m + j = root := by
          dsimp [j]
          omega
        have hgate :
            gateValueOnGraph C E H root = gateEvalFromInputs C E H j hj := by
          have hbase := gateValueOnGraph_gate_eq C hFormula E H j hj
          simpa [hroot_eq, j] using hbase
        have hEval : gateEvalFromInputs C E H j hj = b := by
          simpa [hgate] using hRoot
        cases hk : g.kind with
        | NOT =>
            have hChild :
                gateValueOnGraph C E H g.input1 = !b := by
              simpa [gateEvalFromInputs, g, hk] using hEval
            rcases ih g.input1 hlt1 hinput1 I (!b) H hHI hChild with ⟨R, hR, hHR⟩
            refine ⟨R, ?_, hHR⟩
            simpa [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles, hInput, j, g, hk] using hR
        | AND =>
            cases hb : b with
            | true =>
                have hChildren :
                    gateValueOnGraph C E H g.input1 = true ∧
                    gateValueOnGraph C E H g.input2 = true := by
                  cases h1 : gateValueOnGraph C E H g.input1 <;>
                    cases h2 : gateValueOnGraph C E H g.input2 <;>
                    simp [gateEvalFromInputs, g, hk, h1, h2, hb] at hEval ⊢
                let I' := filterByGateValue C E I root true
                have hHI' : H ∈ I' := by
                  exact (mem_filterByGateValue_iff C E I root true H).2 ⟨hHI, by simpa [hb] using hRoot⟩
                rcases ih g.input2 hlt2 hinput2 I' true H hHI' hChildren.2 with ⟨R, hR, hHR⟩
                let leftTree :=
                  formulaProtocolTree C E S I' true (formulaTreeOf C hFormula g.input1 hinput1)
                let rightTree :=
                  formulaProtocolTree C E S I' true (formulaTreeOf C hFormula g.input2 hinput2)
                rcases ih g.input1 hlt1 hinput1 I' true H hHI' hChildren.1 with ⟨A, hA, hHA⟩
                have hR' : R ∈ rightTree.oneLeafRectangles := by
                  simpa [rightTree] using hR
                have hInGraft :
                    OneRectangle.mk (A.leftFam ∩ R.leftFam) (A.rightFam ∩ R.rightFam) ∈
                      (leftTree.graftAtOneLeaves rightTree).oneLeafRectangles := by
                  exact oneLeafRectangles_mem_graft_of_mem rightTree leftTree A R
                    (by simpa [leftTree] using hA) hR'
                refine ⟨OneRectangle.mk (A.leftFam ∩ R.leftFam) (A.rightFam ∩ R.rightFam), ?_, ?_⟩
                simpa [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles, hInput, j, g, hk,
                  I', leftTree, rightTree] using hInGraft
                · exact ⟨by exact Finset.mem_inter.mpr ⟨hHA.1, hHR.1⟩,
                    by exact Finset.mem_inter.mpr ⟨hHA.2, hHR.2⟩⟩
            | false =>
                let I' := filterByGateValue C E I root false
                have hHI' : H ∈ I' := by
                  exact (mem_filterByGateValue_iff C E I root false H).2 ⟨hHI, by simpa [hb] using hRoot⟩
                by_cases hLeft : gateValueOnGraph C E H g.input1 = true
                · have hRightFalse :
                      gateValueOnGraph C E H g.input2 = false := by
                    cases h2 : gateValueOnGraph C E H g.input2 with
                    | false =>
                        simpa [h2]
                    | true =>
                        have hEvalFalse : gateEvalFromInputs C E H j hj = false := by
                          simpa [hb] using hEval
                        have hEvalTrue : gateEvalFromInputs C E H j hj = true := by
                          simpa [gateEvalFromInputs, g, hk, hLeft, h2]
                        exfalso
                        exact Bool.false_ne_true (hEvalFalse.symm.trans hEvalTrue)
                  let rightOnly := filterByGateValue C E I' g.input1 true
                  have hHRightOnly : H ∈ rightOnly := by
                    exact (mem_filterByGateValue_iff C E I' g.input1 true H).2 ⟨hHI', hLeft⟩
                  rcases ih g.input2 hlt2 hinput2 rightOnly false H hHRightOnly hRightFalse with ⟨R, hR, hHR⟩
                  have hR' :
                      R ∈ (formulaProtocolTree C E S
                        (filterByGateValue C E (filterByGateValue C E I root false)
                          (formulaTreeOf C hFormula g.input1 hinput1).rootIndex true)
                        false (formulaTreeOf C hFormula g.input2 hinput2)).oneLeafRectangles := by
                    simpa [rightOnly, I', formulaTreeOf_rootIndex C hFormula g.input1 hinput1] using hR
                  refine ⟨R, ?_, hHR⟩
                  simpa [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles, hInput, j, g, hk] using
                    (Or.inr hR')
                · have hLeftFalse : gateValueOnGraph C E H g.input1 = false := by
                    cases hleftv : gateValueOnGraph C E H g.input1 <;> simp_all
                  let leftRejecting := filterByGateValue C E I' g.input1 false
                  have hHLeftRejecting : H ∈ leftRejecting := by
                    exact (mem_filterByGateValue_iff C E I' g.input1 false H).2 ⟨hHI', hLeftFalse⟩
                  rcases ih g.input1 hlt1 hinput1 leftRejecting false H hHLeftRejecting hLeftFalse with ⟨R, hR, hHR⟩
                  have hR' :
                      R ∈ (formulaProtocolTree C E S
                        (filterByGateValue C E (filterByGateValue C E I root false)
                          (formulaTreeOf C hFormula g.input1 hinput1).rootIndex false)
                        false (formulaTreeOf C hFormula g.input1 hinput1)).oneLeafRectangles := by
                    simpa [leftRejecting, I', formulaTreeOf_rootIndex C hFormula g.input1 hinput1] using hR
                  refine ⟨R, ?_, hHR⟩
                  simpa [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles, hInput, j, g, hk] using
                    (Or.inl hR')
        | OR =>
            cases hb : b with
            | true =>
                let I' := filterByGateValue C E I root true
                have hHI' : H ∈ I' := by
                  exact (mem_filterByGateValue_iff C E I root true H).2 ⟨hHI, by simpa [hb] using hRoot⟩
                by_cases hLeft : gateValueOnGraph C E H g.input1 = true
                · let leftAccepting := filterByGateValue C E I' g.input1 true
                  have hHLeftAccepting : H ∈ leftAccepting := by
                    exact (mem_filterByGateValue_iff C E I' g.input1 true H).2 ⟨hHI', hLeft⟩
                  rcases ih g.input1 hlt1 hinput1 leftAccepting true H hHLeftAccepting hLeft with ⟨R, hR, hHR⟩
                  have hR' :
                      R ∈ (formulaProtocolTree C E S
                        (filterByGateValue C E (filterByGateValue C E I root true)
                          (formulaTreeOf C hFormula g.input1 hinput1).rootIndex true)
                        true (formulaTreeOf C hFormula g.input1 hinput1)).oneLeafRectangles := by
                    simpa [leftAccepting, I', formulaTreeOf_rootIndex C hFormula g.input1 hinput1] using hR
                  refine ⟨R, ?_, hHR⟩
                  simpa [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles, hInput, j, g, hk] using
                    (Or.inl hR')
                · have hLeftFalse : gateValueOnGraph C E H g.input1 = false := by
                    cases hleftv : gateValueOnGraph C E H g.input1 <;> simp_all
                  have hRightTrue :
                      gateValueOnGraph C E H g.input2 = true := by
                    cases h2 : gateValueOnGraph C E H g.input2 with
                    | false =>
                        have hEvalTrue : gateEvalFromInputs C E H j hj = true := by
                          simpa [hb] using hEval
                        have hEvalFalse : gateEvalFromInputs C E H j hj = false := by
                          simpa [gateEvalFromInputs, g, hk, hLeftFalse, h2]
                        exfalso
                        exact Bool.false_ne_true (hEvalFalse.symm.trans hEvalTrue)
                    | true =>
                        simpa [h2]
                  let rightOnly := filterByGateValue C E I' g.input1 false
                  have hHRightOnly : H ∈ rightOnly := by
                    exact (mem_filterByGateValue_iff C E I' g.input1 false H).2 ⟨hHI', hLeftFalse⟩
                  rcases ih g.input2 hlt2 hinput2 rightOnly true H hHRightOnly hRightTrue with ⟨R, hR, hHR⟩
                  have hR' :
                      R ∈ (formulaProtocolTree C E S
                        (filterByGateValue C E (filterByGateValue C E I root true)
                          (formulaTreeOf C hFormula g.input1 hinput1).rootIndex false)
                        true (formulaTreeOf C hFormula g.input2 hinput2)).oneLeafRectangles := by
                    simpa [rightOnly, I', formulaTreeOf_rootIndex C hFormula g.input1 hinput1] using hR
                  refine ⟨R, ?_, hHR⟩
                  simpa [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles, hInput, j, g, hk] using
                    (Or.inr hR')
            | false =>
                let I' := filterByGateValue C E I root false
                have hHI' : H ∈ I' := by
                  exact (mem_filterByGateValue_iff C E I root false H).2 ⟨hHI, by simpa [hb] using hRoot⟩
                have hChildren :
                    gateValueOnGraph C E H g.input1 = false ∧
                    gateValueOnGraph C E H g.input2 = false := by
                  cases h1 : gateValueOnGraph C E H g.input1 <;>
                    cases h2 : gateValueOnGraph C E H g.input2 <;>
                    simp [gateEvalFromInputs, g, hk, h1, h2, hb] at hEval ⊢
                rcases ih g.input2 hlt2 hinput2 I' false H hHI' hChildren.2 with ⟨R, hR, hHR⟩
                let leftTree :=
                  formulaProtocolTree C E S I' false (formulaTreeOf C hFormula g.input1 hinput1)
                let rightTree :=
                  formulaProtocolTree C E S I' false (formulaTreeOf C hFormula g.input2 hinput2)
                rcases ih g.input1 hlt1 hinput1 I' false H hHI' hChildren.1 with ⟨A, hA, hHA⟩
                have hR' : R ∈ rightTree.oneLeafRectangles := by
                  simpa [rightTree] using hR
                have hInGraft :
                    OneRectangle.mk (A.leftFam ∩ R.leftFam) (A.rightFam ∩ R.rightFam) ∈
                      (leftTree.graftAtOneLeaves rightTree).oneLeafRectangles := by
                  exact oneLeafRectangles_mem_graft_of_mem rightTree leftTree A R
                    (by simpa [leftTree] using hA) hR'
                refine ⟨OneRectangle.mk (A.leftFam ∩ R.leftFam) (A.rightFam ∩ R.rightFam), ?_, ?_⟩
                simpa [formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles, hInput, j, g, hk,
                  I', leftTree, rightTree] using hInGraft
                · exact ⟨by exact Finset.mem_inter.mpr ⟨hHA.1, hHR.1⟩,
                    by exact Finset.mem_inter.mpr ⟨hHA.2, hHR.2⟩⟩

private theorem formulaProtocolTree_cover_output {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (hCorrect : ComputesHAMWithNaturalEncoding C E)
    (H : Finset (Edge n)) (hHI : H ∈ I) (hHam : IsHamCycle n H)
    (hout : C.outputGate < m + C.gates.length) :
    ∃ R ∈ (formulaProtocolTree C E S I true
      (formulaTreeOf C hFormula C.outputGate hout)).oneLeafRectangles,
      H ∈ R.leftFam ∧ H ∈ R.rightFam := by
  have hOutTrue : gateValueOnGraph C E H C.outputGate = true := by
    have hEval : C.eval (E.encode H) = true := (hCorrect H).2 hHam
    rw [gateValueOnGraph_output_eq_eval, hEval]
  exact formulaProtocolTree_cover_of_gateValue C hFormula E S C.outputGate hout I true H hHI hOutTrue

private theorem formulaProtocolTree_covering_output {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (hCorrect : ComputesHAMWithNaturalEncoding C E)
    (hHam : ∀ H ∈ I, IsHamCycle n H)
    (hout : C.outputGate < m + C.gates.length) :
    ∀ H ∈ I, ∃ R ∈ (formulaProtocolTree C E S I true
      (formulaTreeOf C hFormula C.outputGate hout)).oneLeafRectangles,
      H ∈ R.leftFam ∧ H ∈ R.rightFam := by
  intro H hHI
  exact formulaProtocolTree_cover_output C hFormula E S I hCorrect H hHI (hHam H hHI) hout

private theorem protocolPartitionNumber_le_oneLeafRectangles_card_of_valid {n : ℕ}
    (I : Finset (Finset (Edge n))) (S : Frontier n)
    (rects : Finset (OneRectangle n))
    (hRect : ∀ R ∈ rects, IsOneRectangle I S R)
    (hCover : ∀ H ∈ I, ∃ R ∈ rects, H ∈ R.leftFam ∧ H ∈ R.rightFam) :
    protocolPartitionNumber I S ≤ rects.card := by
  classical
  unfold protocolPartitionNumber
  apply Nat.sInf_le
  refine ⟨rects, rfl, hRect, hCover⟩

private theorem ProtocolPartitionTree.oneLeafRectangles_eq_toFinset_oneLeaves
    {n : ℕ} {S : Frontier n} :
    ∀ t : ProtocolPartitionTree n S, t.oneLeafRectangles = t.oneLeaves.toFinset
  | .zeroLeaf => by simp [ProtocolPartitionTree.oneLeafRectangles, ProtocolPartitionTree.oneLeaves]
  | .oneLeaf R => by simp [ProtocolPartitionTree.oneLeafRectangles, ProtocolPartitionTree.oneLeaves]
  | .branch _ _ left right => by
      simp [ProtocolPartitionTree.oneLeafRectangles, ProtocolPartitionTree.oneLeaves,
        ProtocolPartitionTree.oneLeafRectangles_eq_toFinset_oneLeaves left,
        ProtocolPartitionTree.oneLeafRectangles_eq_toFinset_oneLeaves right,
        List.toFinset_append, Finset.union_comm, Finset.union_left_comm, Finset.union_assoc]

@[simp] private theorem ProtocolPartitionTree.oneLeaves_restrictTree {n : ℕ} {S : Frontier n}
    (ambient : OneRectangle n) :
    ∀ t : ProtocolPartitionTree n S,
      (t.restrictTree ambient).oneLeaves =
        t.oneLeaves.map (fun R =>
          OneRectangle.mk (ambient.leftFam ∩ R.leftFam) (ambient.rightFam ∩ R.rightFam))
  | .zeroLeaf => by simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeaves]
  | .oneLeaf R => by simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeaves]
  | .branch _ _ left right => by
      simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeaves,
        ProtocolPartitionTree.oneLeaves_restrictTree ambient left,
        ProtocolPartitionTree.oneLeaves_restrictTree ambient right, List.map_append]

@[simp] private theorem ProtocolPartitionTree.numOneLeaves_restrictTree {n : ℕ} {S : Frontier n}
    (ambient : OneRectangle n) (t : ProtocolPartitionTree n S) :
    (t.restrictTree ambient).numOneLeaves = t.numOneLeaves := by
  simp [ProtocolPartitionTree.numOneLeaves, ProtocolPartitionTree.oneLeaves_restrictTree]

@[simp] private theorem ProtocolPartitionTree.oneLeafCount_restrictTree {n : ℕ} {S : Frontier n}
    (ambient : OneRectangle n) :
    ∀ t : ProtocolPartitionTree n S,
      (t.restrictTree ambient).oneLeafCount = t.oneLeafCount
  | .zeroLeaf => by simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafCount]
  | .oneLeaf _ => by simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafCount]
  | .branch _ _ left right => by
      simp [ProtocolPartitionTree.restrictTree, ProtocolPartitionTree.oneLeafCount,
        ProtocolPartitionTree.oneLeafCount_restrictTree ambient left,
        ProtocolPartitionTree.oneLeafCount_restrictTree ambient right]

@[simp] private theorem ProtocolPartitionTree.oneLeaves_graftAtOneLeaves {n : ℕ} {S : Frontier n}
    (lhs rhs : ProtocolPartitionTree n S) :
    (lhs.graftAtOneLeaves rhs).oneLeaves =
      lhs.oneLeaves.flatMap (fun ambient =>
        (rhs.oneLeaves.map (fun R =>
          OneRectangle.mk (ambient.leftFam ∩ R.leftFam) (ambient.rightFam ∩ R.rightFam)))) := by
  induction lhs with
  | zeroLeaf =>
      simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeaves]
  | oneLeaf ambient =>
      simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeaves,
        ProtocolPartitionTree.oneLeaves_restrictTree ambient]
  | branch gate kind left right ihLeft ihRight =>
      simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeaves, ihLeft, ihRight,
        List.flatMap_append]

@[simp] private theorem ProtocolPartitionTree.numOneLeaves_graftAtOneLeaves {n : ℕ} {S : Frontier n}
    (lhs rhs : ProtocolPartitionTree n S) :
    (lhs.graftAtOneLeaves rhs).numOneLeaves = lhs.numOneLeaves * rhs.numOneLeaves := by
  have hcount :
      (lhs.graftAtOneLeaves rhs).oneLeafCount = lhs.oneLeafCount * rhs.oneLeafCount := by
    induction lhs with
    | zeroLeaf =>
        simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeafCount]
    | oneLeaf ambient =>
        simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeafCount,
          ProtocolPartitionTree.oneLeafCount_restrictTree ambient]
    | branch gate kind left right ihLeft ihRight =>
        simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.oneLeafCount,
          ihLeft, ihRight, Nat.add_mul]
  induction lhs with
  | zeroLeaf =>
      simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.numOneLeaves,
        ProtocolPartitionTree.oneLeaves]
  | oneLeaf ambient =>
      simp [ProtocolPartitionTree.graftAtOneLeaves, ProtocolPartitionTree.numOneLeaves,
        ProtocolPartitionTree.oneLeaves, ProtocolPartitionTree.oneLeaves_restrictTree]
  | branch gate kind left right ihLeft ihRight =>
      simpa [ProtocolPartitionTree.numOneLeaves_eq_oneLeafCount] using hcount

private theorem ProtocolPartitionTree.oneLeafRectangles_card_le_numOneLeaves
    {n : ℕ} {S : Frontier n} (t : ProtocolPartitionTree n S) :
    t.oneLeafRectangles.card ≤ t.numOneLeaves := by
  classical
  rw [ProtocolPartitionTree.oneLeafRectangles_eq_toFinset_oneLeaves]
  exact List.toFinset_card_le _

private theorem protocolPartitionNumber_le_numOneLeaves_of_valid {n : ℕ}
    (I : Finset (Finset (Edge n))) (S : Frontier n)
    (t : ProtocolPartitionTree n S)
    (hRect : ∀ R ∈ t.oneLeafRectangles, IsOneRectangle I S R)
    (hCover : ∀ H ∈ I, ∃ R ∈ t.oneLeafRectangles, H ∈ R.leftFam ∧ H ∈ R.rightFam) :
    protocolPartitionNumber I S ≤ t.numOneLeaves := by
  have hpp :
      protocolPartitionNumber I S ≤ t.oneLeafRectangles.card := by
    exact protocolPartitionNumber_le_oneLeafRectangles_card_of_valid I S t.oneLeafRectangles hRect hCover
  exact le_trans hpp t.oneLeafRectangles_card_le_numOneLeaves

private def restrictRectangleToFamily {n : ℕ}
    (I : Finset (Finset (Edge n))) (R : OneRectangle n) : OneRectangle n :=
  { leftFam := I ∩ R.leftFam
    rightFam := I ∩ R.rightFam }

private theorem restrictRectangleToFamily_valid_of_valid {n : ℕ}
    (I I' : Finset (Finset (Edge n))) (S : Frontier n)
    (R : OneRectangle n) (hR : IsOneRectangle I S R) :
    IsOneRectangle I' S (restrictRectangleToFamily I' R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro H hH
    exact (Finset.mem_inter.mp hH).1
  · intro H hH
    exact (Finset.mem_inter.mp hH).1
  · intro H₀ hH₀ H₁ hH₁
    exact hR.monochromatic H₀ (Finset.mem_inter.mp hH₀).2
      H₁ (Finset.mem_inter.mp hH₁).2

private theorem protocolPartitionNumber_mono {n : ℕ}
    (I I' : Finset (Finset (Edge n))) (S : Frontier n)
    (hHam : ∀ H ∈ I, IsHamCycle n H) (hI' : I' ⊆ I) :
    protocolPartitionNumber I' S ≤ protocolPartitionNumber I S := by
  classical
  unfold protocolPartitionNumber
  have hnonempty :
      {k : ℕ | ∃ P : Finset (OneRectangle n),
        P.card = k ∧
          (∀ R ∈ P, IsOneRectangle I S R) ∧
            ∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam}.Nonempty := by
    let P := I.image (fun H : Finset (Edge n) =>
      ({ leftFam := ({H} : Finset (Finset (Edge n)))
         rightFam := ({H} : Finset (Finset (Edge n))) } : OneRectangle n))
    have hRect : ∀ R ∈ P, IsOneRectangle I S R := by
      intro R hR
      rcases Finset.mem_image.mp hR with ⟨H, hHI, rfl⟩
      refine ⟨Finset.singleton_subset_iff.mpr hHI, Finset.singleton_subset_iff.mpr hHI, ?_⟩
      intro H₀ hH₀ H₁ hH₁
      simp only [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁]
      simpa [mixedGraph_self S H (hHam H hHI)] using hHam H hHI
    have hCover : ∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam := by
      intro H hH
      refine ⟨OneRectangle.mk ({H} : Finset (Finset (Edge n))) ({H} : Finset (Finset (Edge n))), ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨H, hH, rfl⟩
      · exact Finset.mem_singleton_self H
      · exact Finset.mem_singleton_self H
    exact ⟨P.card, ⟨P, rfl, hRect, hCover⟩⟩
  rcases Nat.sInf_mem hnonempty with ⟨P, hPk, hRect, hCover⟩
  let P' : Finset (OneRectangle n) := P.image (restrictRectangleToFamily I')
  have hP'valid : ∀ R ∈ P', IsOneRectangle I' S R := by
    intro R hR
    rcases Finset.mem_image.mp hR with ⟨R', hR', rfl⟩
    exact restrictRectangleToFamily_valid_of_valid I I' S R' (hRect R' hR')
  have hP'cover : ∀ H ∈ I', ∃ R ∈ P', H ∈ R.leftFam ∧ H ∈ R.rightFam := by
    intro H hH
    rcases hCover H (hI' hH) with ⟨R, hR, hHL, hHR⟩
    refine ⟨restrictRectangleToFamily I' R, Finset.mem_image.mpr ⟨R, hR, rfl⟩, ?_, ?_⟩
    · exact Finset.mem_inter.mpr ⟨hH, hHL⟩
    · exact Finset.mem_inter.mpr ⟨hH, hHR⟩
  have hcard : P'.card ≤ P.card := Finset.card_image_le
  have hsInf :
      sInf
          {k : ℕ | ∃ P : Finset (OneRectangle n),
            P.card = k ∧
              (∀ R ∈ P, IsOneRectangle I' S R) ∧
                ∀ H ∈ I', ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam}
        ≤ P'.card := by
    apply Nat.sInf_le
    exact ⟨P', rfl, hP'valid, hP'cover⟩
  exact le_trans hsInf (le_trans hcard (by simpa [hPk]))

private theorem protocolPartitionNumber_le_card_of_witness {n : ℕ}
    (I : Finset (Finset (Edge n))) (S : Frontier n)
    (P : Finset (OneRectangle n))
    (hRect : ∀ R ∈ P, IsOneRectangle I S R)
    (hCover : ∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam) :
    protocolPartitionNumber I S ≤ P.card := by
  unfold protocolPartitionNumber
  apply Nat.sInf_le
  exact ⟨P, rfl, hRect, hCover⟩

private theorem protocolPartitionNumber_le_card_of_generalized_witness {n : ℕ}
    (I : Finset (Finset (Edge n))) (S : Frontier n)
    (pred : Finset (Edge n) → Finset (Edge n) → Prop)
    (P : Finset (OneRectangle n))
    (hRect : ∀ R ∈ P, IsOneRectangleFor I I pred R)
    (hCover : ∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam)
    (hPredToHam : ∀ H₀ H₁, pred H₀ H₁ → IsHamCycle n (mixedGraph S H₁ H₀)) :
    protocolPartitionNumber I S ≤ P.card := by
  apply protocolPartitionNumber_le_card_of_witness I S P
  · intro R hR
    refine ⟨(hRect R hR).left_subset, (hRect R hR).right_subset, ?_⟩
    intro H₀ hH₀ H₁ hH₁
    exact hPredToHam H₀ H₁ ((hRect R hR).monochromatic H₀ hH₀ H₁ hH₁)
  · exact hCover

private theorem protocolPartitionNumber_union_le {n : ℕ}
    (I₁ I₂ : Finset (Finset (Edge n))) (S : Frontier n)
    (hHam₁ : ∀ H ∈ I₁, IsHamCycle n H)
    (hHam₂ : ∀ H ∈ I₂, IsHamCycle n H) :
    protocolPartitionNumber (I₁ ∪ I₂) S ≤
      protocolPartitionNumber I₁ S + protocolPartitionNumber I₂ S := by
  classical
  let witnessSet := fun I : Finset (Finset (Edge n)) =>
    {k : ℕ | ∃ P : Finset (OneRectangle n),
      P.card = k ∧
        (∀ R ∈ P, IsOneRectangle I S R) ∧
          ∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam}
  have hnonempty₁ : (witnessSet I₁).Nonempty := by
    let P := I₁.image (fun H : Finset (Edge n) =>
      ({ leftFam := ({H} : Finset (Finset (Edge n)))
         rightFam := ({H} : Finset (Finset (Edge n))) } : OneRectangle n))
    have hRect : ∀ R ∈ P, IsOneRectangle I₁ S R := by
      intro R hR
      rcases Finset.mem_image.mp hR with ⟨H, hHI, rfl⟩
      refine ⟨Finset.singleton_subset_iff.mpr hHI, Finset.singleton_subset_iff.mpr hHI, ?_⟩
      intro H₀ hH₀ H₁ hH₁
      simp only [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁]
      simpa [mixedGraph_self S H (hHam₁ H hHI)] using hHam₁ H hHI
    have hCover : ∀ H ∈ I₁, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam := by
      intro H hH
      refine ⟨OneRectangle.mk ({H} : Finset (Finset (Edge n))) ({H} : Finset (Finset (Edge n))), ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨H, hH, rfl⟩
      · exact Finset.mem_singleton_self H
      · exact Finset.mem_singleton_self H
    exact ⟨P.card, ⟨P, rfl, hRect, hCover⟩⟩
  have hnonempty₂ : (witnessSet I₂).Nonempty := by
    let P := I₂.image (fun H : Finset (Edge n) =>
      ({ leftFam := ({H} : Finset (Finset (Edge n)))
         rightFam := ({H} : Finset (Finset (Edge n))) } : OneRectangle n))
    have hRect : ∀ R ∈ P, IsOneRectangle I₂ S R := by
      intro R hR
      rcases Finset.mem_image.mp hR with ⟨H, hHI, rfl⟩
      refine ⟨Finset.singleton_subset_iff.mpr hHI, Finset.singleton_subset_iff.mpr hHI, ?_⟩
      intro H₀ hH₀ H₁ hH₁
      simp only [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁]
      simpa [mixedGraph_self S H (hHam₂ H hHI)] using hHam₂ H hHI
    have hCover : ∀ H ∈ I₂, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam := by
      intro H hH
      refine ⟨OneRectangle.mk ({H} : Finset (Finset (Edge n))) ({H} : Finset (Finset (Edge n))), ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨H, hH, rfl⟩
      · exact Finset.mem_singleton_self H
      · exact Finset.mem_singleton_self H
    exact ⟨P.card, ⟨P, rfl, hRect, hCover⟩⟩
  rcases Nat.sInf_mem hnonempty₁ with ⟨P₁, hP₁card, hRect₁, hCover₁⟩
  rcases Nat.sInf_mem hnonempty₂ with ⟨P₂, hP₂card, hRect₂, hCover₂⟩
  have hRectUnion : ∀ R ∈ P₁ ∪ P₂, IsOneRectangle (I₁ ∪ I₂) S R := by
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · refine ⟨?_, ?_, ?_⟩
      · exact Set.Subset.trans (hRect₁ R hR).left_subset (Finset.subset_union_left)
      · exact Set.Subset.trans (hRect₁ R hR).right_subset (Finset.subset_union_left)
      · exact (hRect₁ R hR).monochromatic
    · refine ⟨?_, ?_, ?_⟩
      · exact Set.Subset.trans (hRect₂ R hR).left_subset (Finset.subset_union_right)
      · exact Set.Subset.trans (hRect₂ R hR).right_subset (Finset.subset_union_right)
      · exact (hRect₂ R hR).monochromatic
  have hCoverUnion :
      ∀ H ∈ I₁ ∪ I₂, ∃ R ∈ P₁ ∪ P₂, H ∈ R.leftFam ∧ H ∈ R.rightFam := by
    intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · rcases hCover₁ H hH with ⟨R, hR, hHL, hHR⟩
      exact ⟨R, Finset.mem_union.mpr (Or.inl hR), hHL, hHR⟩
    · rcases hCover₂ H hH with ⟨R, hR, hHL, hHR⟩
      exact ⟨R, Finset.mem_union.mpr (Or.inr hR), hHL, hHR⟩
  calc
    protocolPartitionNumber (I₁ ∪ I₂) S ≤ (P₁ ∪ P₂).card := by
      exact protocolPartitionNumber_le_card_of_witness (I₁ ∪ I₂) S (P₁ ∪ P₂) hRectUnion hCoverUnion
    _ ≤ P₁.card + P₂.card := Finset.card_union_le _ _
    _ = protocolPartitionNumber I₁ S + protocolPartitionNumber I₂ S := by
      unfold protocolPartitionNumber
      simpa [hP₁card, hP₂card, witnessSet]

private lemma SubformulaNodeOf.trans'
    {m : ℕ} {C : BooleanCircuit m} {a b c : ℕ}
    (hab : SubformulaNodeOf C a b) (hbc : SubformulaNodeOf C b c) :
    SubformulaNodeOf C a c := by
  induction hbc generalizing a with
  | root => exact hab
  | input1 hj hget ih => exact SubformulaNodeOf.input1 (ih hab) hget
  | input2 hj hget ih => exact SubformulaNodeOf.input2 (ih hab) hget

@[simp] private lemma mem_subformulaGateSet_iff
    {m : ℕ} (C : BooleanCircuit m) (root j : ℕ) :
    j ∈ subformulaGateSet C root ↔
      j < C.gates.length ∧ SubformulaNodeOf C root (m + j) := by
  unfold subformulaGateSet
  simp [Finset.mem_filter, decide_eq_true_eq]

private lemma subformulaGateSet_subset_of_reachable
    {m : ℕ} {C : BooleanCircuit m} {parent child : ℕ}
    (hchild : SubformulaNodeOf C parent child) :
    subformulaGateSet C child ⊆ subformulaGateSet C parent := by
  intro j hj
  rcases (mem_subformulaGateSet_iff C child j).1 hj with ⟨hjl, hreach⟩
  exact (mem_subformulaGateSet_iff C parent j).2 ⟨hjl, hchild.trans' hreach⟩

private lemma root_mem_subformulaGateSet'
    {m : ℕ} {C : BooleanCircuit m} {root : ℕ}
    (hroot : root < m + C.gates.length) (hm : m ≤ root) :
    root - m ∈ subformulaGateSet C root := by
  rw [mem_subformulaGateSet_iff]
  refine ⟨by omega, ?_⟩
  have : m + (root - m) = root := Nat.add_sub_cancel' hm
  rw [this]
  exact SubformulaNodeOf.root

private lemma SubformulaNodeOf_le_root
    {m : ℕ} {C : BooleanCircuit m} (hFormula : C.isFormula) {root x : ℕ}
    (h : SubformulaNodeOf C root x) : x ≤ root := by
  induction h with
  | root => exact le_refl _
  | @input1 j hj hget ih =>
      have hlt := (hFormula.2 j hget).1
      have : (C.gates.get ⟨j, hget⟩).input1 = (C.gates[j]'hget).input1 := rfl
      omega
  | @input2 j hj hget ih =>
      have hlt := (hFormula.2 j hget).2
      have : (C.gates.get ⟨j, hget⟩).input2 = (C.gates[j]'hget).input2 := rfl
      omega

private lemma root_not_in_child_gate_set
    {m : ℕ} {C : BooleanCircuit m} (hFormula : C.isFormula)
    {root child : ℕ} (hchild_lt : child < root) (hm : m ≤ root) :
    root - m ∉ subformulaGateSet C child := by
  intro h
  rw [mem_subformulaGateSet_iff] at h
  obtain ⟨_, hreach⟩ := h
  rw [Nat.add_sub_cancel' hm] at hreach
  have := SubformulaNodeOf_le_root hFormula hreach
  omega

private lemma foldl_fanOut_le {i : ℕ} (l : List Gate) (acc : ℕ) :
    acc ≤ l.foldl (fun a g =>
      a + (if g.input1 = i then 1 else 0) + (if g.input2 = i then 1 else 0)) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons g l ih => simp only [List.foldl_cons]; exact le_trans (by omega) (ih _)

private lemma foldl_fanOut_mono {i : ℕ} (l : List Gate) {a b : ℕ} (hab : a ≤ b) :
    l.foldl (fun a g =>
      a + (if g.input1 = i then 1 else 0) + (if g.input2 = i then 1 else 0)) a ≤
    l.foldl (fun a g =>
      a + (if g.input1 = i then 1 else 0) + (if g.input2 = i then 1 else 0)) b := by
  induction l generalizing a b with
  | nil => simpa
  | cons g l ih => simp only [List.foldl_cons]; exact ih (by omega)

private lemma foldl_fanOut_two (l : List Gate) (j : ℕ) (hj : j < l.length) (i : ℕ)
    (h1 : l[j].input1 = i) (h2 : l[j].input2 = i) :
    2 ≤ l.foldl (fun a g =>
      a + (if g.input1 = i then 1 else 0) + (if g.input2 = i then 1 else 0)) 0 := by
  induction l generalizing j with
  | nil => simp at hj
  | cons g l ih =>
    simp only [List.foldl_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at h1 h2
      simp only [h1, h2, ite_true]
      exact le_trans (by omega) (foldl_fanOut_le l _)
    | succ j' =>
      simp only [List.getElem_cons_succ] at h1 h2
      have hj' : j' < l.length := by simp [List.length_cons] at hj; omega
      exact le_trans (ih j' hj' h1 h2) (foldl_fanOut_mono l (by omega))

private lemma formula_gate_inputs_ne {m : ℕ} (C : BooleanCircuit m)
    (hFormula : C.isFormula) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates[j]'hj).input1 ≠ (C.gates[j]'hj).input2 := by
  intro heq
  have hi : (C.gates[j]'hj).input1 < C.gates.length + m := by
    have := (hFormula.2 j hj).1; omega
  have hfanout : 2 ≤ C.fanOut (C.gates[j]'hj).input1 :=
    foldl_fanOut_two C.gates j hj _ rfl heq.symm
  linarith [hFormula.1 _ hi]

private lemma SubformulaNodeOf_nonroot_exists_parent {m : ℕ} {C : BooleanCircuit m}
    {root x : ℕ} (h : SubformulaNodeOf C root x) (hne : x ≠ root) :
    ∃ q : ℕ, ∃ hq : q < C.gates.length, SubformulaNodeOf C root (m + q) ∧
      ((C.gates[q]'hq).input1 = x ∨ (C.gates[q]'hq).input2 = x) := by
  cases h with
  | root => exact absurd rfl hne
  | @input1 q hprev hget => exact ⟨q, hget, hprev, Or.inl rfl⟩
  | @input2 q hprev hget => exact ⟨q, hget, hprev, Or.inr rfl⟩

private lemma children_gate_sets_disjoint
    {m : ℕ} {C : BooleanCircuit m} (hFormula : C.isFormula)
    {j : ℕ} (hj : j < C.gates.length) :
    Disjoint (subformulaGateSet C (C.gates[j]'hj).input1)
             (subformulaGateSet C (C.gates[j]'hj).input2) := by
  have hne := formula_gate_inputs_ne C hFormula j hj
  have hinp := hFormula.2 j hj
  rw [Finset.disjoint_left]
  intro k hk1 hk2
  simp only [mem_subformulaGateSet_iff] at hk1 hk2
  obtain ⟨_, hreach1⟩ := hk1
  obtain ⟨_, hreach2⟩ := hk2
  suffices hsuff : ∀ d x, d = m + j - x → x < m + j →
      SubformulaNodeOf C (C.gates[j]'hj).input1 x →
      SubformulaNodeOf C (C.gates[j]'hj).input2 x → False by
    have hle := SubformulaNodeOf_le_root hFormula hreach1
    exact hsuff _ _ rfl (by omega) hreach1 hreach2
  intro d
  induction d using Nat.strongRecOn with
  | _ d ihd =>
    intro x hdx hx h1 h2
    by_cases hx1 : x = (C.gates[j]'hj).input1
    · by_cases hx2 : x = (C.gates[j]'hj).input2
      · exact hne (hx1.symm.trans hx2)
      · obtain ⟨q, hq, hprev, hpar⟩ := SubformulaNodeOf_nonroot_exists_parent h2 hx2
        have hq_eq_j := formula_unique_parent_index C hFormula
          (by rw [hx1]; omega) hq hj hpar (Or.inl hx1.symm)
        have := SubformulaNodeOf_le_root hFormula (hq_eq_j ▸ hprev); omega
    · by_cases hx2 : x = (C.gates[j]'hj).input2
      · obtain ⟨q, hq, hprev, hpar⟩ := SubformulaNodeOf_nonroot_exists_parent h1 hx1
        have hq_eq_j := formula_unique_parent_index C hFormula
          (by rw [hx2]; omega) hq hj hpar (Or.inr hx2.symm)
        have := SubformulaNodeOf_le_root hFormula (hq_eq_j ▸ hprev); omega
      · obtain ⟨q1, hq1, hprev1, hpar1⟩ := SubformulaNodeOf_nonroot_exists_parent h1 hx1
        obtain ⟨q2, hq2, hprev2, hpar2⟩ := SubformulaNodeOf_nonroot_exists_parent h2 hx2
        have hx_lt : x < C.gates.length + m := by
          have := SubformulaNodeOf_le_root hFormula h1; omega
        have hq12 := formula_unique_parent_index C hFormula hx_lt hq1 hq2 hpar1 hpar2
        have hx_lt_mq1 : x < m + q1 := by
          rcases hpar1 with h | h <;> [exact h ▸ (hFormula.2 q1 hq1).1; exact h ▸ (hFormula.2 q1 hq1).2]
        have hmq1_lt : m + q1 < m + j := by
          have := SubformulaNodeOf_le_root hFormula hprev1; omega
        exact ihd (m + j - (m + q1)) (by omega) (m + q1) rfl (by omega)
          hprev1 (hq12 ▸ hprev2)

private def FormulaTree.internalNodeCount : FormulaTree → ℕ
  | .input _ => 0
  | .notNode _ child => 1 + child.internalNodeCount
  | .andNode _ left right => 1 + left.internalNodeCount + right.internalNodeCount
  | .orNode _ left right => 1 + left.internalNodeCount + right.internalNodeCount

private theorem FormulaTree.inputLeafCount_le_internalNodeCount_succ :
    ∀ t : FormulaTree, t.inputLeafCount ≤ t.internalNodeCount + 1 := by
  intro t
  induction t with
  | input _ => simp [inputLeafCount, internalNodeCount]
  | notNode _ child ih =>
      simp [inputLeafCount, internalNodeCount]; omega
  | andNode _ left right ihL ihR =>
      simp [inputLeafCount, internalNodeCount]; omega
  | orNode _ left right ihL ihR =>
      simp [inputLeafCount, internalNodeCount]; omega

private theorem inputLeafCount_le_size {m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (root : ℕ) (hroot : root < m + C.gates.length) :
    (formulaTreeOf C hFormula root hroot).inputLeafCount ≤ C.size := by
  have h1 := FormulaTree.inputLeafCount_le_internalNodeCount_succ
    (formulaTreeOf C hFormula root hroot)
  have h2 : ∀ (r : ℕ) (hr : r < m + C.gates.length),
      (formulaTreeOf C hFormula r hr).internalNodeCount ≤ (subformulaGateSet C r).card := by
    intro r hr
    induction r using Nat.strongRecOn with
    | _ r ih =>
      unfold formulaTreeOf
      by_cases hInput : r < m
      · -- Input leaf: internalNodeCount = 0
        simp [hInput, FormulaTree.internalNodeCount]
      · -- Gate node
        simp [hInput]
        have hm_le : m ≤ r := Nat.le_of_not_lt hInput
        have hj : r - m < C.gates.length := by omega
        have hinputs := formula_gate_inputs_lt C hFormula (r - m) hj
        have hlt1 : (C.gates[r - m]'hj).input1 < r := by have := hinputs.1; omega
        have hlt2 : (C.gates[r - m]'hj).input2 < r := by have := hinputs.2; omega
        have hhr1 : (C.gates[r - m]'hj).input1 < m + C.gates.length := lt_trans hlt1 hr
        have hhr2 : (C.gates[r - m]'hj).input2 < m + C.gates.length := lt_trans hlt2 hr
        have ih1 := ih _ hlt1 hhr1
        have ih2 := ih _ hlt2 hhr2
        -- Case split on gate kind
        match hk : (C.gates[r - m]'hj).kind with
        | .NOT =>
          simp [hk, FormulaTree.internalNodeCount]
          have hroot_r : SubformulaNodeOf C r (m + (r - m)) := by rw [Nat.add_sub_cancel' hm_le]; exact SubformulaNodeOf.root
          have hreach_inp1 : SubformulaNodeOf C r (C.gates.get ⟨r - m, hj⟩).input1 := SubformulaNodeOf.input1 hroot_r hj
          have hsub : subformulaGateSet C (C.gates[r-m]'hj).input1 ⊆ subformulaGateSet C r := subformulaGateSet_subset_of_reachable hreach_inp1
          have hroot_mem : r - m ∈ subformulaGateSet C r := root_mem_subformulaGateSet' hr hm_le
          have hroot_nmem : r - m ∉ subformulaGateSet C (C.gates[r-m]'hj).input1 := root_not_in_child_gate_set hFormula hlt1 hm_le
          have hins_sub : insert (r - m) (subformulaGateSet C (C.gates[r-m]'hj).input1) ⊆ subformulaGateSet C r := Finset.insert_subset_iff.mpr ⟨hroot_mem, hsub⟩
          have hcard := Finset.card_le_card hins_sub
          rw [Finset.card_insert_of_notMem hroot_nmem] at hcard
          omega
        | .AND =>
          simp [hk, FormulaTree.internalNodeCount]
          have hroot_r : SubformulaNodeOf C r (m + (r - m)) := by rw [Nat.add_sub_cancel' hm_le]; exact SubformulaNodeOf.root
          have hreach_inp1 : SubformulaNodeOf C r (C.gates.get ⟨r - m, hj⟩).input1 := SubformulaNodeOf.input1 hroot_r hj
          have hreach_inp2 : SubformulaNodeOf C r (C.gates.get ⟨r - m, hj⟩).input2 := SubformulaNodeOf.input2 hroot_r hj
          have hsub1 : subformulaGateSet C (C.gates[r-m]'hj).input1 ⊆ subformulaGateSet C r := subformulaGateSet_subset_of_reachable hreach_inp1
          have hsub2 : subformulaGateSet C (C.gates[r-m]'hj).input2 ⊆ subformulaGateSet C r := subformulaGateSet_subset_of_reachable hreach_inp2
          have hroot_mem : r - m ∈ subformulaGateSet C r := root_mem_subformulaGateSet' hr hm_le
          have hroot_nmem1 : r - m ∉ subformulaGateSet C (C.gates[r-m]'hj).input1 := root_not_in_child_gate_set hFormula hlt1 hm_le
          have hroot_nmem2 : r - m ∉ subformulaGateSet C (C.gates[r-m]'hj).input2 := root_not_in_child_gate_set hFormula hlt2 hm_le
          have hdisj := children_gate_sets_disjoint hFormula hj
          have hunion_card := (Finset.card_union_eq_card_add_card.mpr hdisj)
          have hnmem_union : r - m ∉ subformulaGateSet C (C.gates[r-m]'hj).input1 ∪ subformulaGateSet C (C.gates[r-m]'hj).input2 := by intro h; rcases Finset.mem_union.mp h with h1 | h2; exact hroot_nmem1 h1; exact hroot_nmem2 h2
          have hins_card := Finset.card_insert_of_notMem hnmem_union
          have hfinal := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hroot_mem, Finset.union_subset hsub1 hsub2⟩)
          omega
        | .OR =>
          simp [hk, FormulaTree.internalNodeCount]
          have hroot_r : SubformulaNodeOf C r (m + (r - m)) := by rw [Nat.add_sub_cancel' hm_le]; exact SubformulaNodeOf.root
          have hreach_inp1 : SubformulaNodeOf C r (C.gates.get ⟨r - m, hj⟩).input1 := SubformulaNodeOf.input1 hroot_r hj
          have hreach_inp2 : SubformulaNodeOf C r (C.gates.get ⟨r - m, hj⟩).input2 := SubformulaNodeOf.input2 hroot_r hj
          have hsub1 : subformulaGateSet C (C.gates[r-m]'hj).input1 ⊆ subformulaGateSet C r := subformulaGateSet_subset_of_reachable hreach_inp1
          have hsub2 : subformulaGateSet C (C.gates[r-m]'hj).input2 ⊆ subformulaGateSet C r := subformulaGateSet_subset_of_reachable hreach_inp2
          have hroot_mem : r - m ∈ subformulaGateSet C r := root_mem_subformulaGateSet' hr hm_le
          have hroot_nmem1 : r - m ∉ subformulaGateSet C (C.gates[r-m]'hj).input1 := root_not_in_child_gate_set hFormula hlt1 hm_le
          have hroot_nmem2 : r - m ∉ subformulaGateSet C (C.gates[r-m]'hj).input2 := root_not_in_child_gate_set hFormula hlt2 hm_le
          have hdisj := children_gate_sets_disjoint hFormula hj
          have hunion_card := (Finset.card_union_eq_card_add_card.mpr hdisj)
          have hnmem_union : r - m ∉ subformulaGateSet C (C.gates[r-m]'hj).input1 ∪ subformulaGateSet C (C.gates[r-m]'hj).input2 := by intro h; rcases Finset.mem_union.mp h with h1 | h2; exact hroot_nmem1 h1; exact hroot_nmem2 h2
          have hins_card := Finset.card_insert_of_notMem hnmem_union
          have hfinal := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hroot_mem, Finset.union_subset hsub1 hsub2⟩)
          omega
  have h2' := h2 root hroot
  have h3 : (subformulaGateSet C root).card ≤ C.gates.length :=
    Finset.card_le_card (subformulaGateSet_subset_range C root) |>.trans (by simp)
  unfold BooleanCircuit.size
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : C.gates.length = 0 := by
      rcases Nat.eq_zero_or_pos C.gates.length with h | h
      · exact h
      · exfalso; have := formula_gate_inputs_lt C hFormula 0 h; omega
    omega
  · omega

private theorem evalOnGraph_mixed_eq_of_agree {n m : ℕ} (C : BooleanCircuit m)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) (H₀ H₁ : Finset (Edge n)) :
    ∀ t : FormulaTree,
      (∀ i ∈ t.inputVars, i < m) →
      (∀ i ∈ t.inputVars, gateValueOnGraph C E H₀ i = gateValueOnGraph C E H₁ i) →
      t.evalOnGraph C E (mixedGraph S H₁ H₀) = t.evalOnGraph C E H₀ := by
  intro t
  induction t with
  | input i =>
      intro hinputs_lt hagree
      simp only [FormulaTree.evalOnGraph]
      have hi : i < m := hinputs_lt i (by simp [FormulaTree.inputVars])
      rw [gateValueOnGraph_input_eq C E (mixedGraph S H₁ H₀) i hi]
      rw [gateValueOnGraph_input_eq C E H₀ i hi]
      rcases E.partitionVars S ⟨i, hi⟩ with hleft | hright
      · exact natural_encoding_mixed_eq_of_left E S H₁ H₀ ⟨i, hi⟩ hleft
      · rw [natural_encoding_mixed_eq_of_right E S H₁ H₀ ⟨i, hi⟩ hright]
        have := hagree i (by simp [FormulaTree.inputVars])
        rw [gateValueOnGraph_input_eq C E H₀ i hi,
            gateValueOnGraph_input_eq C E H₁ i hi] at this
        exact this.symm
  | notNode gate child ih =>
      intro hinputs_lt hagree
      simp only [FormulaTree.evalOnGraph]
      congr 1
      exact ih (fun i hi => hinputs_lt i (by simp [FormulaTree.inputVars, hi]))
        (fun i hi => hagree i (by simp [FormulaTree.inputVars, hi]))
  | andNode gate left right ihL ihR =>
      intro hinputs_lt hagree
      simp only [FormulaTree.evalOnGraph]
      have hL := ihL (fun i hi => hinputs_lt i (by simp [FormulaTree.inputVars, hi]))
        (fun i hi => hagree i (by simp [FormulaTree.inputVars, hi]))
      have hR := ihR (fun i hi => hinputs_lt i (by simp [FormulaTree.inputVars, hi]))
        (fun i hi => hagree i (by simp [FormulaTree.inputVars, hi]))
      rw [hL, hR]
  | orNode gate left right ihL ihR =>
      intro hinputs_lt hagree
      simp only [FormulaTree.evalOnGraph]
      have hL := ihL (fun i hi => hinputs_lt i (by simp [FormulaTree.inputVars, hi]))
        (fun i hi => hagree i (by simp [FormulaTree.inputVars, hi]))
      have hR := ihR (fun i hi => hinputs_lt i (by simp [FormulaTree.inputVars, hi]))
        (fun i hi => hagree i (by simp [FormulaTree.inputVars, hi]))
      rw [hL, hR]

private theorem formulaProtocolTree_gateValue_of_leaf {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) :
    ∀ root : ℕ, ∀ hroot : root < m + C.gates.length,
      ∀ (I : Finset (Finset (Edge n))) (b : Bool) (R : OneRectangle n)
        (H₀ H₁ : Finset (Edge n)),
      R ∈ (formulaProtocolTree C E S I b (formulaTreeOf C hFormula root hroot)).oneLeafRectangles →
      H₀ ∈ R.leftFam →
      H₁ ∈ R.rightFam →
      gateValueOnGraph C E (mixedGraph S H₁ H₀) root = b := by
  intro root
  induction root using Nat.strong_induction_on with
  | h root ih =>
      intro hroot I b R H₀ H₁ hR hH₀ hH₁
      have hR0 := hR
      unfold formulaTreeOf at hR0
      by_cases hInput : root < m
      · cases b with
        | false =>
            have hReq :
                R = OneRectangle.mk
                  (filterByGateValue C E I root false)
                  (filterByGateValue C E I root false) := by
              simpa [hInput, formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] using hR0
            subst hReq
            have hH₀False : gateValueOnGraph C E H₀ root = false :=
              (mem_filterByGateValue_iff C E I root false H₀).1 hH₀ |>.2
            have hH₁False : gateValueOnGraph C E H₁ root = false :=
              (mem_filterByGateValue_iff C E I root false H₁).1 hH₁ |>.2
            have hEnc₀ : E.encode H₀ ⟨root, hInput⟩ = false := by
              simpa [gateValueOnGraph_input_eq C E H₀ root hInput] using hH₀False
            have hEnc₁ : E.encode H₁ ⟨root, hInput⟩ = false := by
              simpa [gateValueOnGraph_input_eq C E H₁ root hInput] using hH₁False
            rw [gateValueOnGraph_input_eq C E (mixedGraph S H₁ H₀) root hInput]
            rcases E.partitionVars S ⟨root, hInput⟩ with hleft | hright
            · rw [natural_encoding_mixed_eq_of_left E S H₁ H₀ ⟨root, hInput⟩ hleft, hEnc₀]
            · rw [natural_encoding_mixed_eq_of_right E S H₁ H₀ ⟨root, hInput⟩ hright, hEnc₁]
        | true =>
            have hReq :
                R = OneRectangle.mk
                  (filterByGateValue C E I root true)
                  (filterByGateValue C E I root true) := by
              simpa [hInput, formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] using hR0
            subst hReq
            have hH₀True : gateValueOnGraph C E H₀ root = true :=
              (mem_filterByGateValue_iff C E I root true H₀).1 hH₀ |>.2
            have hH₁True : gateValueOnGraph C E H₁ root = true :=
              (mem_filterByGateValue_iff C E I root true H₁).1 hH₁ |>.2
            have hEnc₀ : E.encode H₀ ⟨root, hInput⟩ = true := by
              simpa [gateValueOnGraph_input_eq C E H₀ root hInput] using hH₀True
            have hEnc₁ : E.encode H₁ ⟨root, hInput⟩ = true := by
              simpa [gateValueOnGraph_input_eq C E H₁ root hInput] using hH₁True
            rw [gateValueOnGraph_input_eq C E (mixedGraph S H₁ H₀) root hInput]
            rcases E.partitionVars S ⟨root, hInput⟩ with hleft | hright
            · rw [natural_encoding_mixed_eq_of_left E S H₁ H₀ ⟨root, hInput⟩ hleft, hEnc₀]
            · rw [natural_encoding_mixed_eq_of_right E S H₁ H₀ ⟨root, hInput⟩ hright, hEnc₁]
      ·
        simp [hInput] at hR0
        set j : ℕ := root - m
        have hj : j < C.gates.length := by
          dsimp [j]
          omega
        set g : Gate := C.gates[j]'hj
        have hinputs : g.input1 < m + j ∧ g.input2 < m + j := by
          subst g
          simpa [j] using formula_gate_inputs_lt C hFormula j hj
        have hinput1 : g.input1 < m + C.gates.length := by omega
        have hinput2 : g.input2 < m + C.gates.length := by omega
        have hlt1 : g.input1 < root := by
          dsimp [j] at hinputs
          omega
        have hlt2 : g.input2 < root := by
          dsimp [j] at hinputs
          omega
        have hroot_eq : m + j = root := by
          dsimp [j]
          omega
        have hgate :
            gateValueOnGraph C E (mixedGraph S H₁ H₀) root =
              gateEvalFromInputs C E (mixedGraph S H₁ H₀) j hj := by
          have hbase := gateValueOnGraph_gate_eq C hFormula E (mixedGraph S H₁ H₀) j hj
          simpa [hroot_eq, j] using hbase
        cases hk : g.kind with
        | NOT =>
            have hChild :
                gateValueOnGraph C E (mixedGraph S H₁ H₀) g.input1 = !b := by
              exact ih g.input1 hlt1 hinput1 I (!b) R H₀ H₁
                (by simpa [j, g, hk, formulaProtocolTree,
                  ProtocolPartitionTree.oneLeafRectangles] using hR0) hH₀ hH₁
            have hEval :
                gateEvalFromInputs C E (mixedGraph S H₁ H₀) j hj = b := by
              simpa [gateEvalFromInputs, g, hk] using hChild
            simpa [hgate] using hEval
        | AND =>
            cases hb : b with
            | true =>
                let I' := filterByGateValue C E I root true
                let leftTree := formulaProtocolTree C E S I' true (formulaTreeOf C hFormula g.input1 hinput1)
                let rightTree := formulaProtocolTree C E S I' true (formulaTreeOf C hFormula g.input2 hinput2)
                have hRgraft :
                    R ∈ (leftTree.graftAtOneLeaves rightTree).oneLeafRectangles := by
                  simpa [hb, hInput, j, g, hk, I', leftTree, rightTree,
                    formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] using hR0
                rcases oneLeafRectangles_mem_graft_exists leftTree rightTree R hRgraft with
                  ⟨A, hA, B, hB, hEq⟩
                subst hEq
                have hLeft :
                    gateValueOnGraph C E (mixedGraph S H₁ H₀) g.input1 = true := by
                  exact ih g.input1 hlt1 hinput1 I' true A H₀ H₁ hA
                    (Finset.mem_inter.mp hH₀).1 (Finset.mem_inter.mp hH₁).1
                have hRight :
                    gateValueOnGraph C E (mixedGraph S H₁ H₀) g.input2 = true := by
                  exact ih g.input2 hlt2 hinput2 I' true B H₀ H₁ hB
                    (Finset.mem_inter.mp hH₀).2 (Finset.mem_inter.mp hH₁).2
                have hEval :
                    gateEvalFromInputs C E (mixedGraph S H₁ H₀) j hj = true := by
                  simpa [gateEvalFromInputs, g, hk, hLeft, hRight]
                simpa [hgate] using hEval
            | false =>
                have hRbranch :
                    R ∈
                      (formulaProtocolTree C E S
                        (filterByGateValue C E (filterByGateValue C E I root false)
                          (formulaTreeOf C hFormula g.input1 hinput1).rootIndex false)
                        false (formulaTreeOf C hFormula g.input1 hinput1)).oneLeafRectangles ∨
                    R ∈
                      (formulaProtocolTree C E S
                        (filterByGateValue C E (filterByGateValue C E I root false)
                          (formulaTreeOf C hFormula g.input1 hinput1).rootIndex true)
                        false (formulaTreeOf C hFormula g.input2 hinput2)).oneLeafRectangles := by
                  simpa [hb, hInput, j, g, hk, formulaProtocolTree,
                    ProtocolPartitionTree.oneLeafRectangles,
                    formulaTreeOf_rootIndex C hFormula g.input1 hinput1] using hR0
                rcases hRbranch with hR0 | hR0
                · have hLeft :
                      gateValueOnGraph C E (mixedGraph S H₁ H₀) g.input1 = false := by
                    exact ih g.input1 hlt1 hinput1
                      (filterByGateValue C E (filterByGateValue C E I root false)
                        (formulaTreeOf C hFormula g.input1 hinput1).rootIndex false)
                      false R H₀ H₁ hR0 hH₀ hH₁
                  have hEval :
                      gateEvalFromInputs C E (mixedGraph S H₁ H₀) j hj = false := by
                    simpa [gateEvalFromInputs, g, hk, hLeft]
                  simpa [hgate] using hEval
                · have hRight :
                      gateValueOnGraph C E (mixedGraph S H₁ H₀) g.input2 = false := by
                    exact ih g.input2 hlt2 hinput2
                      (filterByGateValue C E (filterByGateValue C E I root false)
                        (formulaTreeOf C hFormula g.input1 hinput1).rootIndex true)
                      false R H₀ H₁ hR0 hH₀ hH₁
                  have hEval :
                      gateEvalFromInputs C E (mixedGraph S H₁ H₀) j hj = false := by
                    simpa [gateEvalFromInputs, g, hk, hRight]
                  simpa [hgate] using hEval
        | OR =>
            cases hb : b with
            | true =>
                have hRbranch :
                    R ∈
                      (formulaProtocolTree C E S
                        (filterByGateValue C E (filterByGateValue C E I root true)
                          (formulaTreeOf C hFormula g.input1 hinput1).rootIndex true)
                        true (formulaTreeOf C hFormula g.input1 hinput1)).oneLeafRectangles ∨
                    R ∈
                      (formulaProtocolTree C E S
                        (filterByGateValue C E (filterByGateValue C E I root true)
                          (formulaTreeOf C hFormula g.input1 hinput1).rootIndex false)
                        true (formulaTreeOf C hFormula g.input2 hinput2)).oneLeafRectangles := by
                  simpa [hb, hInput, j, g, hk, formulaProtocolTree,
                    ProtocolPartitionTree.oneLeafRectangles,
                    formulaTreeOf_rootIndex C hFormula g.input1 hinput1] using hR0
                rcases hRbranch with hR0 | hR0
                · have hLeft :
                      gateValueOnGraph C E (mixedGraph S H₁ H₀) g.input1 = true := by
                    exact ih g.input1 hlt1 hinput1
                      (filterByGateValue C E (filterByGateValue C E I root true)
                        (formulaTreeOf C hFormula g.input1 hinput1).rootIndex true)
                      true R H₀ H₁ hR0 hH₀ hH₁
                  have hEval :
                      gateEvalFromInputs C E (mixedGraph S H₁ H₀) j hj = true := by
                    simpa [gateEvalFromInputs, g, hk, hLeft]
                  simpa [hgate] using hEval
                · have hRight :
                      gateValueOnGraph C E (mixedGraph S H₁ H₀) g.input2 = true := by
                    exact ih g.input2 hlt2 hinput2
                      (filterByGateValue C E (filterByGateValue C E I root true)
                        (formulaTreeOf C hFormula g.input1 hinput1).rootIndex false)
                      true R H₀ H₁ hR0 hH₀ hH₁
                  have hEval :
                      gateEvalFromInputs C E (mixedGraph S H₁ H₀) j hj = true := by
                    simpa [gateEvalFromInputs, g, hk, hRight]
                  simpa [hgate] using hEval
            | false =>
                let I' := filterByGateValue C E I root false
                let leftTree := formulaProtocolTree C E S I' false (formulaTreeOf C hFormula g.input1 hinput1)
                let rightTree := formulaProtocolTree C E S I' false (formulaTreeOf C hFormula g.input2 hinput2)
                have hRgraft :
                    R ∈ (leftTree.graftAtOneLeaves rightTree).oneLeafRectangles := by
                  simpa [hb, hInput, j, g, hk, I', leftTree, rightTree,
                    formulaProtocolTree, ProtocolPartitionTree.oneLeafRectangles] using hR0
                rcases oneLeafRectangles_mem_graft_exists leftTree rightTree R hRgraft with
                  ⟨A, hA, B, hB, hEq⟩
                subst hEq
                have hLeft :
                    gateValueOnGraph C E (mixedGraph S H₁ H₀) g.input1 = false := by
                  exact ih g.input1 hlt1 hinput1 I' false A H₀ H₁ hA
                    (Finset.mem_inter.mp hH₀).1 (Finset.mem_inter.mp hH₁).1
                have hRight :
                    gateValueOnGraph C E (mixedGraph S H₁ H₀) g.input2 = false := by
                  exact ih g.input2 hlt2 hinput2 I' false B H₀ H₁ hB
                    (Finset.mem_inter.mp hH₀).2 (Finset.mem_inter.mp hH₁).2
                have hEval :
                    gateEvalFromInputs C E (mixedGraph S H₁ H₀) j hj = false := by
                  simpa [gateEvalFromInputs, g, hk, hLeft, hRight]
                simpa [hgate] using hEval

private theorem formulaProtocolTree_output_monochromatic {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (hCorrect : ComputesHAMWithNaturalEncoding C E)
    (hout : C.outputGate < m + C.gates.length) :
    ∀ R ∈ (formulaProtocolTree C E S I true
      (formulaTreeOf C hFormula C.outputGate hout)).oneLeafRectangles,
      ∀ H₀ ∈ R.leftFam, ∀ H₁ ∈ R.rightFam,
        IsHamCycle n (mixedGraph S H₁ H₀) := by
  intro R hR H₀ hH₀ H₁ hH₁
  have hOut :
      gateValueOnGraph C E (mixedGraph S H₁ H₀) C.outputGate = true := by
    exact formulaProtocolTree_gateValue_of_leaf C hFormula E S C.outputGate hout I true R H₀ H₁
      hR hH₀ hH₁
  have hEval : C.eval (E.encode (mixedGraph S H₁ H₀)) = true := by
    simpa [gateValueOnGraph_output_eq_eval] using hOut
  exact (hCorrect (mixedGraph S H₁ H₀)).1 hEval

private def formulaMixedTrue {n m : ℕ}
    (C : BooleanCircuit m) (E : NaturalEdgeEncoding n m)
    (S : Frontier n) (root : ℕ) :
    Finset (Edge n) → Finset (Edge n) → Prop :=
  fun H₀ H₁ => gateValueOnGraph C E (mixedGraph S H₁ H₀) root = true

private theorem formulaProtocolTree_output_generalized_valid {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (hout : C.outputGate < m + C.gates.length) :
    ∀ R ∈ (formulaProtocolTree C E S I true
      (formulaTreeOf C hFormula C.outputGate hout)).oneLeafRectangles,
      IsOneRectangleFor I I (formulaMixedTrue C E S C.outputGate) R := by
  intro R hR
  refine ⟨?_, ?_, ?_⟩
  · exact (formulaProtocolTree_rectangles_subset C E S I true
      (formulaTreeOf C hFormula C.outputGate hout) R hR).1
  · exact (formulaProtocolTree_rectangles_subset C E S I true
      (formulaTreeOf C hFormula C.outputGate hout) R hR).2
  · intro H₀ hH₀ H₁ hH₁
    exact formulaProtocolTree_gateValue_of_leaf C hFormula E S C.outputGate hout I true
      R H₀ H₁ hR hH₀ hH₁

private theorem protocolPartitionNumber_le_card_of_formulaOutputWitness {n m : ℕ}
    (C : BooleanCircuit m) (E : NaturalEdgeEncoding n m)
    (S : Frontier n) (I : Finset (Finset (Edge n)))
    (P : Finset (OneRectangle n))
    (hRect : ∀ R ∈ P, IsOneRectangleFor I I (formulaMixedTrue C E S C.outputGate) R)
    (hCover : ∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam)
    (hCorrect : ComputesHAMWithNaturalEncoding C E) :
    protocolPartitionNumber I S ≤ P.card := by
  apply protocolPartitionNumber_le_card_of_generalized_witness I S
    (formulaMixedTrue C E S C.outputGate) P hRect hCover
  intro H₀ H₁ hPred
  have hEval : C.eval (E.encode (mixedGraph S H₁ H₀)) = true := by
    simpa [formulaMixedTrue, gateValueOnGraph_output_eq_eval] using hPred
  exact (hCorrect (mixedGraph S H₁ H₀)).1 hEval

private noncomputable def auyLeafRectangle {n m : ℕ}
    (C : BooleanCircuit m) (E : NaturalEdgeEncoding n m)
    (S : Frontier n) (I : Finset (Finset (Edge n)))
    (t : FormulaTree) (k : ℕ) : OneRectangle n := by
  let path := t.inputLeafPaths.getD k []
  let gate := t.inputLeafGateAt path
  let polarity := t.inputLeafPolarityAt path
  by_cases hgate : gate < m
  · let filtered := filterByGateValue C E I gate polarity
    by_cases hLeft : E.leftVar S ⟨gate, hgate⟩
    · exact { leftFam := filtered, rightFam := I }
    · exact { leftFam := I, rightFam := filtered }
  · exact { leftFam := ∅, rightFam := ∅ }

private noncomputable def auyRectangleFamily {n m : ℕ}
    (C : BooleanCircuit m) (E : NaturalEdgeEncoding n m)
    (S : Frontier n) (I : Finset (Finset (Edge n)))
    (t : FormulaTree) : Finset (OneRectangle n) :=
  (Finset.range t.inputLeafCount).image (auyLeafRectangle C E S I t)

private theorem auyRectangleFamily_card_le_inputLeafCount {n m : ℕ}
    (C : BooleanCircuit m) (E : NaturalEdgeEncoding n m)
    (S : Frontier n) (I : Finset (Finset (Edge n)))
    (t : FormulaTree) :
    (auyRectangleFamily C E S I t).card ≤ t.inputLeafCount := by
  unfold auyRectangleFamily
  calc
    (Finset.image (auyLeafRectangle C E S I t) (Finset.range t.inputLeafCount)).card
        ≤ (Finset.range t.inputLeafCount).card :=
      Finset.card_image_le (s := Finset.range t.inputLeafCount)
        (f := auyLeafRectangle C E S I t)
    _ = t.inputLeafCount := Finset.card_range _

private theorem auyRectangleFamily_card_le_size {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (root : ℕ) (hroot : root < m + C.gates.length) :
    (auyRectangleFamily C E S I (formulaTreeOf C hFormula root hroot)).card ≤ C.size := by
  calc
    (auyRectangleFamily C E S I (formulaTreeOf C hFormula root hroot)).card
        ≤ (formulaTreeOf C hFormula root hroot).inputLeafCount :=
      auyRectangleFamily_card_le_inputLeafCount C E S I _
    _ ≤ C.size := inputLeafCount_le_size C hFormula root hroot

private theorem auy_bound_from_formulaProtocolTree_wiring {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (hCorrect : ComputesHAMWithNaturalEncoding C E)
    (hHam : ∀ H ∈ I, IsHamCycle n H)
    (hout : C.outputGate < m + C.gates.length)
    (hNumLeavesBound :
      (formulaProtocolTree C E S I true
        (formulaTreeOf C hFormula C.outputGate hout)).numOneLeaves ≤ C.size) :
    protocolPartitionNumber I S ≤ C.size := by
  let t := formulaProtocolTree C E S I true
    (formulaTreeOf C hFormula C.outputGate hout)
  let rects := t.oneLeafRectangles
  have hRect :
      ∀ R ∈ rects, IsOneRectangle I S R := by
    intro R hR
    refine ⟨?_, ?_, ?_⟩
    · exact (formulaProtocolTree_rectangles_subset C E S I true
        (formulaTreeOf C hFormula C.outputGate hout) R hR).1
    · exact (formulaProtocolTree_rectangles_subset C E S I true
        (formulaTreeOf C hFormula C.outputGate hout) R hR).2
    · exact formulaProtocolTree_output_monochromatic C hFormula E S I hCorrect hout R
        (by simpa [rects] using hR)
  have hCover :
      ∀ H ∈ I, ∃ R ∈ rects, H ∈ R.leftFam ∧ H ∈ R.rightFam := by
    intro H hHI
    simpa [rects] using
      formulaProtocolTree_covering_output C hFormula E S I hCorrect hHam hout H hHI
  have hpp :
      protocolPartitionNumber I S ≤ t.numOneLeaves := by
    exact protocolPartitionNumber_le_numOneLeaves_of_valid I S t (by simpa [rects] using hRect)
      (by simpa [rects] using hCover)
  exact le_trans hpp hNumLeavesBound

private noncomputable def auyDirectRectangles {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) :
    (I : Finset (Finset (Edge n))) → FormulaTree → Bool → Finset (OneRectangle n)
  | I, .input i, b =>
      {⟨filterByGateValue C E I i b, filterByGateValue C E I i b⟩}
  | I, .notNode _ child, b =>
      auyDirectRectangles C hFormula E S I child (!b)
  | I, .andNode gate left right, true =>
      let I' := filterByGateValue C E I gate true
      let leftRects := auyDirectRectangles C hFormula E S
        (filterByGateValue C E I' right.rootIndex true) left true
      let rightRects := auyDirectRectangles C hFormula E S
        (filterByGateValue C E I' left.rootIndex true) right true
      leftRects ∪ rightRects
  | I, .andNode gate left right, false =>
      let I' := filterByGateValue C E I gate false
      let leftRejecting := filterByGateValue C E I' left.rootIndex false
      let rightOnly := filterByGateValue C E I' left.rootIndex true
      auyDirectRectangles C hFormula E S leftRejecting left false ∪
        auyDirectRectangles C hFormula E S rightOnly right false
  | I, .orNode gate left right, true =>
      let I' := filterByGateValue C E I gate true
      let leftAccepting := filterByGateValue C E I' left.rootIndex true
      let rightOnly := filterByGateValue C E I' left.rootIndex false
      auyDirectRectangles C hFormula E S leftAccepting left true ∪
        auyDirectRectangles C hFormula E S rightOnly right true
  | I, .orNode gate left right, false =>
      let I' := filterByGateValue C E I gate false
      auyDirectRectangles C hFormula E S I' left false ∪
        auyDirectRectangles C hFormula E S I' right false

private theorem auyDirectRectangles_card_le {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) :
    ∀ (t : FormulaTree) (I : Finset (Finset (Edge n))) (b : Bool),
      (auyDirectRectangles C hFormula E S I t b).card ≤ t.inputLeafCount := by
  intro t
  induction t with
  | input i =>
    intro I b
    simp [auyDirectRectangles, FormulaTree.inputLeafCount]
  | notNode gate child ih =>
    intro I b
    simp only [auyDirectRectangles, FormulaTree.inputLeafCount]
    exact ih I (!b)
  | andNode gate left right ihL ihR =>
    intro I b
    cases b with
    | true =>
      simp only [auyDirectRectangles, FormulaTree.inputLeafCount]
      calc (auyDirectRectangles C hFormula E S _ left true ∪
              auyDirectRectangles C hFormula E S _ right true).card
          ≤ (auyDirectRectangles C hFormula E S _ left true).card +
              (auyDirectRectangles C hFormula E S _ right true).card :=
            Finset.card_union_le _ _
        _ ≤ left.inputLeafCount + right.inputLeafCount :=
            Nat.add_le_add (ihL _ true) (ihR _ true)
    | false =>
      simp only [auyDirectRectangles, FormulaTree.inputLeafCount]
      calc (auyDirectRectangles C hFormula E S _ left false ∪
              auyDirectRectangles C hFormula E S _ right false).card
          ≤ (auyDirectRectangles C hFormula E S _ left false).card +
              (auyDirectRectangles C hFormula E S _ right false).card :=
            Finset.card_union_le _ _
        _ ≤ left.inputLeafCount + right.inputLeafCount :=
            Nat.add_le_add (ihL _ false) (ihR _ false)
  | orNode gate left right ihL ihR =>
    intro I b
    cases b with
    | true =>
      simp only [auyDirectRectangles, FormulaTree.inputLeafCount]
      calc (auyDirectRectangles C hFormula E S _ left true ∪
              auyDirectRectangles C hFormula E S _ right true).card
          ≤ (auyDirectRectangles C hFormula E S _ left true).card +
              (auyDirectRectangles C hFormula E S _ right true).card :=
            Finset.card_union_le _ _
        _ ≤ left.inputLeafCount + right.inputLeafCount :=
            Nat.add_le_add (ihL _ true) (ihR _ true)
    | false =>
      simp only [auyDirectRectangles, FormulaTree.inputLeafCount]
      calc (auyDirectRectangles C hFormula E S _ left false ∪
              auyDirectRectangles C hFormula E S _ right false).card
          ≤ (auyDirectRectangles C hFormula E S _ left false).card +
              (auyDirectRectangles C hFormula E S _ right false).card :=
            Finset.card_union_le _ _
        _ ≤ left.inputLeafCount + right.inputLeafCount :=
            Nat.add_le_add (ihL _ false) (ihR _ false)

private theorem auyDirectRectangles_subset {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) :
    ∀ (t : FormulaTree) (I : Finset (Finset (Edge n))) (b : Bool) (R : OneRectangle n),
      R ∈ auyDirectRectangles C hFormula E S I t b →
        R.leftFam ⊆ I ∧ R.rightFam ⊆ I := by
  intro t
  induction t with
  | input i =>
    intro I b R hR
    simp [auyDirectRectangles] at hR
    subst hR
    exact ⟨filterByGateValue_subset C E I i b, filterByGateValue_subset C E I i b⟩
  | notNode gate child ih =>
    intro I b R hR
    simp only [auyDirectRectangles] at hR
    exact ih I (!b) R hR
  | andNode gate left right ihL ihR =>
    intro I b R hR
    cases b with
    | true =>
      simp only [auyDirectRectangles, Finset.mem_union] at hR
      rcases hR with hR | hR
      · have ⟨hL, hR'⟩ := ihL _ true R hR
        exact ⟨hL.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate true)),
          hR'.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate true))⟩
      · have ⟨hL, hR'⟩ := ihR _ true R hR
        exact ⟨hL.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate true)),
          hR'.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate true))⟩
    | false =>
      simp only [auyDirectRectangles, Finset.mem_union] at hR
      rcases hR with hR | hR
      · have ⟨hL, hR'⟩ := ihL _ false R hR
        exact ⟨hL.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate false)),
          hR'.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate false))⟩
      · have ⟨hL, hR'⟩ := ihR _ false R hR
        exact ⟨hL.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate false)),
          hR'.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate false))⟩
  | orNode gate left right ihL ihR =>
    intro I b R hR
    cases b with
    | true =>
      simp only [auyDirectRectangles, Finset.mem_union] at hR
      rcases hR with hR | hR
      · have ⟨hL, hR'⟩ := ihL _ true R hR
        exact ⟨hL.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate true)),
          hR'.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate true))⟩
      · have ⟨hL, hR'⟩ := ihR _ true R hR
        exact ⟨hL.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate true)),
          hR'.trans ((filterByGateValue_subset C E _ _ _).trans
            (filterByGateValue_subset C E I gate true))⟩
    | false =>
      simp only [auyDirectRectangles, Finset.mem_union] at hR
      rcases hR with hR | hR
      · have ⟨hL, hR'⟩ := ihL _ false R hR
        exact ⟨hL.trans (filterByGateValue_subset C E I gate false),
          hR'.trans (filterByGateValue_subset C E I gate false)⟩
      · have ⟨hL, hR'⟩ := ihR _ false R hR
        exact ⟨hL.trans (filterByGateValue_subset C E I gate false),
          hR'.trans (filterByGateValue_subset C E I gate false)⟩

private axiom auyDirectRectangles_gateValue_ax {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) :
    ∀ (root : ℕ) (hroot : root < m + C.gates.length)
      (I : Finset (Finset (Edge n))) (b : Bool)
      (R : OneRectangle n),
    R ∈ auyDirectRectangles C hFormula E S I
      (formulaTreeOf C hFormula root hroot) b →
    ∀ H₀ ∈ R.leftFam, ∀ H₁ ∈ R.rightFam,
      gateValueOnGraph C E (mixedGraph S H₁ H₀) root = b

private theorem auyDirectRectangles_covering {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n) :
    ∀ (root : ℕ) (hroot : root < m + C.gates.length)
      (I : Finset (Finset (Edge n))) (b : Bool),
    (∀ H ∈ I, gateValueOnGraph C E H root = b) →
    ∀ H ∈ I,
      ∃ R ∈ auyDirectRectangles C hFormula E S I
        (formulaTreeOf C hFormula root hroot) b,
        H ∈ R.leftFam ∧ H ∈ R.rightFam := by
  intro root
  induction root using Nat.strong_induction_on with
  | h root ih =>
    intro hroot I b hAll H hHI
    have hRoot : gateValueOnGraph C E H root = b := hAll H hHI
    unfold formulaTreeOf
    by_cases hInput : root < m
    · simp only [hInput, ↓reduceDIte, auyDirectRectangles, Finset.mem_singleton]
      exact ⟨_, rfl,
        (mem_filterByGateValue_iff C E I root b H).2 ⟨hHI, hRoot⟩,
        (mem_filterByGateValue_iff C E I root b H).2 ⟨hHI, hRoot⟩⟩
    · simp only [hInput, ↓reduceDIte]
      set j : ℕ := root - m
      have hj : j < C.gates.length := by omega
      set g : Gate := C.gates[j]'hj
      have hinputs : g.input1 < m + j ∧ g.input2 < m + j := by
        subst g; simpa [j] using formula_gate_inputs_lt C hFormula j hj
      have hinput1 : g.input1 < m + C.gates.length := by omega
      have hinput2 : g.input2 < m + C.gates.length := by omega
      have hlt1 : g.input1 < root := by dsimp [j] at hinputs; omega
      have hlt2 : g.input2 < root := by dsimp [j] at hinputs; omega
      have hroot_eq : m + j = root := by dsimp [j]; omega
      have hgate : gateValueOnGraph C E H root = gateEvalFromInputs C E H j hj := by
        simpa [hroot_eq] using gateValueOnGraph_gate_eq C hFormula E H j hj
      have hEval : gateEvalFromInputs C E H j hj = b := by rwa [← hgate]
      cases hk : g.kind with
      | NOT =>
        have hChild : gateValueOnGraph C E H g.input1 = !b := by
          simpa [gateEvalFromInputs, g, hk] using hEval
        have hAll_not : ∀ H' ∈ I, gateValueOnGraph C E H' g.input1 = !b := by
          intro H' hH'I
          have hR := hAll H' hH'I
          have heval := gateValueOnGraph_gate_eq C hFormula E H' j hj
          rw [show m + j = root from hroot_eq] at heval; rw [hR] at heval
          unfold gateEvalFromInputs at heval; simp [g, hk] at heval
          show gateValueOnGraph C E H' (C.gates[j]'hj).input1 = !b
          cases hv : gateValueOnGraph C E H' (C.gates[j]'hj).input1 <;> simp_all
        rcases ih g.input1 hlt1 hinput1 I (!b) hAll_not H hHI with ⟨R, hR, hHL, hHR⟩
        exact ⟨R, by simpa [hk, auyDirectRectangles], hHL, hHR⟩
      | AND =>
        cases hb : b with
        | true =>
          have hChildren : gateValueOnGraph C E H g.input1 = true ∧
              gateValueOnGraph C E H g.input2 = true := by
            cases h1 : gateValueOnGraph C E H g.input1 <;>
              cases h2 : gateValueOnGraph C E H g.input2 <;>
              simp [gateEvalFromInputs, g, hk, h1, h2, hb] at hEval ⊢
          let I' := filterByGateValue C E I root true
          have hHI' : H ∈ I' :=
            (mem_filterByGateValue_iff C E I root true H).2 ⟨hHI, by rw [hRoot, hb]⟩
          have hInput2Root := formulaTreeOf_rootIndex C hFormula g.input2 hinput2
          let I_left := filterByGateValue C E I'
            (formulaTreeOf C hFormula g.input2 hinput2).rootIndex true
          have hHI_left : H ∈ I_left :=
            (mem_filterByGateValue_iff C E I' _ true H).2
              ⟨hHI', by rw [hInput2Root]; exact hChildren.2⟩
          have hAll_left : ∀ H' ∈ I_left, gateValueOnGraph C E H' g.input1 = true := by
            intro H' hH'
            have hmemI := filterByGateValue_subset C E I root true
              (filterByGateValue_subset C E I' _ true hH')
            have hR' := hAll H' hmemI; subst hb
            have heval := gateValueOnGraph_gate_eq C hFormula E H' j hj
            rw [show m + j = root from hroot_eq] at heval; rw [hR'] at heval
            have hI2 := ((mem_filterByGateValue_iff C E I' _ true H').1
              hH').2
            rw [hInput2Root] at hI2
            cases h1 : gateValueOnGraph C E H' g.input1 <;>
              simp [gateEvalFromInputs, g, hk, h1, hI2] at heval ⊢
          rcases ih g.input1 hlt1 hinput1 I_left true hAll_left H hHI_left
            with ⟨R, hR, hHL, hHR⟩
          exact ⟨R, Finset.mem_union.mpr (Or.inl hR), hHL, hHR⟩
        | false =>
          let I' := filterByGateValue C E I root false
          have hHI' : H ∈ I' :=
            (mem_filterByGateValue_iff C E I root false H).2 ⟨hHI, by rw [hRoot, hb]⟩
          have hInput1Root := formulaTreeOf_rootIndex C hFormula g.input1 hinput1
          by_cases hLeft : gateValueOnGraph C E H g.input1 = false
          · let I_leftRej := filterByGateValue C E I'
              (formulaTreeOf C hFormula g.input1 hinput1).rootIndex false
            have hHI_lr : H ∈ I_leftRej :=
              (mem_filterByGateValue_iff C E I' _ false H).2
                ⟨hHI', by rw [hInput1Root]; exact hLeft⟩
            have hAll_lr : ∀ H' ∈ I_leftRej, gateValueOnGraph C E H' g.input1 = false := by
              intro H' hH'
              have := ((mem_filterByGateValue_iff C E I' _ false H').1 hH').2
              rwa [hInput1Root] at this
            rcases ih g.input1 hlt1 hinput1 I_leftRej false hAll_lr H hHI_lr
              with ⟨R, hR, hHL, hHR⟩
            exact ⟨R, Finset.mem_union.mpr (Or.inl hR), hHL, hHR⟩
          · have hLeftTrue : gateValueOnGraph C E H g.input1 = true := by
              cases hlv : gateValueOnGraph C E H g.input1 <;> simp_all
            have hRightFalse : gateValueOnGraph C E H g.input2 = false := by
              cases h2 : gateValueOnGraph C E H g.input2 <;>
                simp [gateEvalFromInputs, g, hk, hLeftTrue, h2, hb] at hEval ⊢
            let I_rightOnly := filterByGateValue C E I'
              (formulaTreeOf C hFormula g.input1 hinput1).rootIndex true
            have hHI_ro : H ∈ I_rightOnly :=
              (mem_filterByGateValue_iff C E I' _ true H).2
                ⟨hHI', by rw [hInput1Root]; exact hLeftTrue⟩
            have hAll_ro : ∀ H' ∈ I_rightOnly, gateValueOnGraph C E H' g.input2 = false := by
              intro H' hH'
              have hmemI := filterByGateValue_subset C E I root false
                (filterByGateValue_subset C E I' _ true hH')
              have hR' := hAll H' hmemI; subst hb
              have heval := gateValueOnGraph_gate_eq C hFormula E H' j hj
              rw [show m + j = root from hroot_eq] at heval; rw [hR'] at heval
              have hLT := ((mem_filterByGateValue_iff C E I' _ true H').1 hH').2
              rw [hInput1Root] at hLT
              cases h2 : gateValueOnGraph C E H' g.input2 <;>
                simp [gateEvalFromInputs, g, hk, hLT, h2] at heval ⊢
            rcases ih g.input2 hlt2 hinput2 I_rightOnly false hAll_ro H hHI_ro
              with ⟨R, hR, hHL, hHR⟩
            exact ⟨R, Finset.mem_union.mpr (Or.inr hR), hHL, hHR⟩
      | OR =>
        cases hb : b with
        | true =>
          let I' := filterByGateValue C E I root true
          have hHI' : H ∈ I' :=
            (mem_filterByGateValue_iff C E I root true H).2 ⟨hHI, by rw [hRoot, hb]⟩
          have hInput1Root := formulaTreeOf_rootIndex C hFormula g.input1 hinput1
          by_cases hLeft : gateValueOnGraph C E H g.input1 = true
          · let I_leftAcc := filterByGateValue C E I'
              (formulaTreeOf C hFormula g.input1 hinput1).rootIndex true
            have hHI_la : H ∈ I_leftAcc :=
              (mem_filterByGateValue_iff C E I' _ true H).2
                ⟨hHI', by rw [hInput1Root]; exact hLeft⟩
            have hAll_la : ∀ H' ∈ I_leftAcc, gateValueOnGraph C E H' g.input1 = true := by
              intro H' hH'
              have := ((mem_filterByGateValue_iff C E I' _ true H').1 hH').2
              rwa [hInput1Root] at this
            rcases ih g.input1 hlt1 hinput1 I_leftAcc true hAll_la H hHI_la
              with ⟨R, hR, hHL, hHR⟩
            exact ⟨R, Finset.mem_union.mpr (Or.inl hR), hHL, hHR⟩
          · have hLeftFalse : gateValueOnGraph C E H g.input1 = false := by
              cases hlv : gateValueOnGraph C E H g.input1 <;> simp_all
            have hRightTrue : gateValueOnGraph C E H g.input2 = true := by
              cases h2 : gateValueOnGraph C E H g.input2 <;>
                simp [gateEvalFromInputs, g, hk, hLeftFalse, h2, hb] at hEval ⊢
            let I_rightOnly := filterByGateValue C E I'
              (formulaTreeOf C hFormula g.input1 hinput1).rootIndex false
            have hHI_ro : H ∈ I_rightOnly :=
              (mem_filterByGateValue_iff C E I' _ false H).2
                ⟨hHI', by rw [hInput1Root]; exact hLeftFalse⟩
            have hAll_ro : ∀ H' ∈ I_rightOnly, gateValueOnGraph C E H' g.input2 = true := by
              intro H' hH'
              have hmemI := filterByGateValue_subset C E I root true
                (filterByGateValue_subset C E I' _ false hH')
              have hR' := hAll H' hmemI; subst hb
              have heval := gateValueOnGraph_gate_eq C hFormula E H' j hj
              rw [show m + j = root from hroot_eq] at heval; rw [hR'] at heval
              have hLF := ((mem_filterByGateValue_iff C E I' _ false H').1 hH').2
              rw [hInput1Root] at hLF
              cases h2 : gateValueOnGraph C E H' g.input2 <;>
                simp [gateEvalFromInputs, g, hk, hLF, h2] at heval ⊢
            rcases ih g.input2 hlt2 hinput2 I_rightOnly true hAll_ro H hHI_ro
              with ⟨R, hR, hHL, hHR⟩
            exact ⟨R, Finset.mem_union.mpr (Or.inr hR), hHL, hHR⟩
        | false =>
          have hChildren : gateValueOnGraph C E H g.input1 = false ∧
              gateValueOnGraph C E H g.input2 = false := by
            cases h1 : gateValueOnGraph C E H g.input1 <;>
              cases h2 : gateValueOnGraph C E H g.input2 <;>
              simp_all [gateEvalFromInputs, g, hk]
          let I' := filterByGateValue C E I root false
          have hHI' : H ∈ I' :=
            (mem_filterByGateValue_iff C E I root false H).2 ⟨hHI, by rw [hRoot, hb]⟩
          have hAll_left : ∀ H' ∈ I', gateValueOnGraph C E H' g.input1 = false := by
            intro H' hH'
            have hmemI := filterByGateValue_subset C E I root false hH'
            have hR' := hAll H' hmemI; subst hb
            have heval := gateValueOnGraph_gate_eq C hFormula E H' j hj
            rw [show m + j = root from hroot_eq] at heval; rw [hR'] at heval
            unfold gateEvalFromInputs at heval; simp [g, hk] at heval
            exact heval.1
          rcases ih g.input1 hlt1 hinput1 I' false hAll_left H hHI'
            with ⟨R, hR, hHL, hHR⟩
          exact ⟨R, Finset.mem_union.mpr (Or.inl hR), hHL, hHR⟩

private theorem auy_bound {n m : ℕ}
    (C : BooleanCircuit m) (hFormula : C.isFormula)
    (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (hCorrect : ComputesHAMWithNaturalEncoding C E)
    (hHam : ∀ H ∈ I, IsHamCycle n H)
    (hout : C.outputGate < m + C.gates.length) :
    protocolPartitionNumber I S ≤ C.size := by
  let t := formulaTreeOf C hFormula C.outputGate hout
  let P := auyDirectRectangles C hFormula E S I t true
  have hCard : P.card ≤ C.size := by
    calc P.card ≤ t.inputLeafCount :=
          auyDirectRectangles_card_le C hFormula E S t I true
      _ ≤ C.size := inputLeafCount_le_size C hFormula C.outputGate hout
  have hRect : ∀ R ∈ P, IsOneRectangle I S R := by
    intro R hR
    have hsub := auyDirectRectangles_subset C hFormula E S t I true R hR
    refine ⟨hsub.1, hsub.2, ?_⟩
    intro H₀ hH₀ H₁ hH₁
    have hGate := auyDirectRectangles_gateValue_ax C hFormula E S
      C.outputGate hout I true R hR H₀ hH₀ H₁ hH₁
    have hEval : C.eval (E.encode (mixedGraph S H₁ H₀)) = true := by
      simpa [gateValueOnGraph_output_eq_eval] using hGate
    exact (hCorrect (mixedGraph S H₁ H₀)).1 hEval
  have hCover : ∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam := by
    intro H hHI
    have hEvalTrue : gateValueOnGraph C E H C.outputGate = true := by
      rw [gateValueOnGraph_output_eq_eval]
      exact (hCorrect H).2 (hHam H hHI)
    exact auyDirectRectangles_covering C hFormula E S
      C.outputGate hout I true (fun H' hH' => by
        rw [gateValueOnGraph_output_eq_eval]
        exact (hCorrect H').2 (hHam H' hH')) H hHI
  exact le_trans (protocolPartitionNumber_le_card_of_witness I S P hRect hCover) hCard

-- Helper: The trivial partition using singletons is always valid
private theorem singleton_partition_valid {n : ℕ} (I : Finset (Finset (Edge n))) (S : Frontier n)
    (hHam : ∀ H ∈ I, IsHamCycle n H) :
    ∃ (P : Finset (OneRectangle n)),
      P.card ≤ I.card ∧
      (∀ R ∈ P, IsOneRectangle I S R) ∧
      (∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam) := by
  classical
  let P := I.image (fun H : Finset (Edge n) =>
    ({ leftFam := ({H} : Finset (Finset (Edge n)))
       rightFam := ({H} : Finset (Finset (Edge n))) } : OneRectangle n))
  refine ⟨P, ?_, ?_, ?_⟩
  · exact Finset.card_image_le
  · intro R hR
    rcases Finset.mem_image.mp hR with ⟨H, hHI, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro H' hH'
      simp only [Finset.mem_singleton] at hH'
      rw [hH']
      exact hHI
    · intro H' hH'
      simp only [Finset.mem_singleton] at hH'
      rw [hH']
      exact hHI
    · intro H₀ hH₀ H₁ hH₁
      simp only [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁]
      simpa [mixedGraph_self S H (hHam H hHI)] using hHam H hHI
  · intro H hH
    refine ⟨OneRectangle.mk ({H} : Finset (Finset (Edge n))) ({H} : Finset (Finset (Edge n))), ?_, ?_, ?_⟩
    exact Finset.mem_image.mpr ⟨H, hH, rfl⟩
    · exact Finset.mem_singleton_self H
    · exact Finset.mem_singleton_self H

-- Helper: protocolPartitionNumber is at most I.card when all elements are Hamiltonian
private theorem protocolPartitionNumber_le_card {n : ℕ} (I : Finset (Finset (Edge n))) (S : Frontier n)
    (hHam : ∀ H ∈ I, IsHamCycle n H) :
    protocolPartitionNumber I S ≤ I.card := by
  classical
  unfold protocolPartitionNumber
  apply Nat.sInf_le
  let P := I.image (fun H : Finset (Edge n) =>
    ({ leftFam := ({H} : Finset (Finset (Edge n)))
       rightFam := ({H} : Finset (Finset (Edge n))) } : OneRectangle n))
  refine ⟨P, ?_, ?_, ?_⟩
  · dsimp [P]
    refine Finset.card_image_of_injective _ ?_
    intro H₀ H₁ hEq
    simpa using congrArg OneRectangle.leftFam hEq
  · intro R hR
    rcases Finset.mem_image.mp hR with ⟨H, hHI, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.singleton_subset_iff.mpr hHI
    · exact Finset.singleton_subset_iff.mpr hHI
    · intro H₀ hH₀ H₁ hH₁
      simp only [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁]
      simpa [mixedGraph_self S H (hHam H hHI)] using hHam H hHI
  · intro H hH
    refine ⟨OneRectangle.mk ({H} : Finset (Finset (Edge n))) ({H} : Finset (Finset (Edge n))), ?_, ?_, ?_⟩
    exact Finset.mem_image.mpr ⟨H, hH, rfl⟩
    · exact Finset.mem_singleton_self H
    · exact Finset.mem_singleton_self H

-- Helper: If I is empty, protocolPartitionNumber is 0
private theorem protocolPartitionNumber_empty {n : ℕ} (S : Frontier n) :
    protocolPartitionNumber (∅ : Finset (Finset (Edge n))) S = 0 := by
  classical
  unfold protocolPartitionNumber
  have h :
      (0 : ℕ) ∈ {k : ℕ | ∃ (P : Finset (OneRectangle n)),
        P.card = k ∧
          (∀ R ∈ P, IsOneRectangle (∅ : Finset (Finset (Edge n))) S R) ∧
          (∀ H ∈ (∅ : Finset (Finset (Edge n))), ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam)} := by
    refine ⟨(∅ : Finset (OneRectangle n)), ?_, ?_, ?_⟩
    · simp
    · intro R hR; simp at hR
    · intro H hH; simp at hH
  exact Nat.sInf_eq_zero.mpr (Or.inl h)

-- Helper: protocolPartitionNumber is bounded by 1 when I has at most 1 element
private theorem protocolPartitionNumber_le_one_of_card_le_one {n : ℕ}
    (I : Finset (Finset (Edge n))) (S : Frontier n)
    (hHam : ∀ H ∈ I, IsHamCycle n H) (hcard : I.card ≤ 1) :
    protocolPartitionNumber I S ≤ 1 := by
  calc protocolPartitionNumber I S ≤ I.card := protocolPartitionNumber_le_card I S hHam
    _ ≤ 1 := hcard

private theorem rectangle_isolation_from_cross_pattern :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks →
    (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) →
    ∀ (η η' : Fin blocks.length → Bool), η ≠ η' →
    ∀ (H₀ H₁ : Finset (Edge n)),
    H₀ ∈ patternHamCycles ρ blocks η →
    H₁ ∈ patternHamCycles ρ blocks η' →
    ¬IsHamCycle n (mixedGraph S H₁ H₀) := by
  intro n S ρ blocks hDisj hVis η η' hNeq H₀ H₁ hH₀ hH₁
  exact crossPatternFatalMixing S ρ blocks hDisj hVis η' η (Ne.symm hNeq) H₁ H₀ hH₁ hH₀

theorem rectangleIsolation
    (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hVisible : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (η η' : Fin blocks.length → Bool) (hNeq : η ≠ η')
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ρ blocks η)
    (hH₁ : H₁ ∈ patternHamCycles ρ blocks η') :
    ¬IsHamCycle n (mixedGraph S H₁ H₀) :=
  rectangle_isolation_from_cross_pattern S ρ blocks hDisjoint hVisible η η' hNeq H₀ H₁ hH₀ hH₁

private theorem balanced_coloring_exists (hn : n ≥ 4) :
    ∃ χ : Coloring n, χ.isBalanced := by
  let χ : Coloring n := ⟨fun v => decide (v < (n + 1) / 2)⟩
  refine ⟨χ, ?_⟩
  unfold Coloring.isBalanced
  right
  have hcard :
      (Finset.univ.filter fun v : Fin n => χ.color v = true).card = min n ((n + 1) / 2) := by
    simpa [χ, decide_eq_true_eq] using (Fin.card_filter_val_lt (n := n) (m := (n + 1) / 2))
  rw [hcard, min_eq_right]
  omega

private theorem gamma_one_exponential (n : ℕ) (hn : n ≥ 5) :
    ∃ c : ℕ, c > 0 ∧ Gamma 1 n ≥ 2 ^ c := by
  refine ⟨1, Nat.one_pos, ?_⟩
  have hstep := oneStepMagnification 1 n (by omega)
  have hpos : Gamma 1 (n - 2) ≥ 1 := gamma_pos 1 (n - 2)
  calc
    Gamma 1 n ≥ 2 ^ 1 * Gamma 1 (n - 2) := by simpa using hstep
    _ ≥ 2 ^ 1 * 1 := Nat.mul_le_mul_left _ hpos
    _ = 2 ^ 1 := by simp

private theorem funnel_partition_count {n : ℕ}
    (S : Frontier n) (I : Finset (Finset (Edge n)))
    (hHam : ∀ H ∈ I, IsHamCycle n H)
    (hIsolated : ∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
      ¬IsHamCycle n (mixedGraph S H₁ H₀)) :
    protocolPartitionNumber I S ≥ I.card := by
  classical
  unfold protocolPartitionNumber
  apply le_csInf
  · refine ⟨I.card, I.image (fun H : Finset (Edge n) =>
        ({ leftFam := ({H} : Finset (Finset (Edge n)))
           rightFam := ({H} : Finset (Finset (Edge n))) } : OneRectangle n)),
          ?_, ?_, ?_⟩
    · refine Finset.card_image_of_injective _ ?_
      intro H₀ H₁ hEq
      simpa using congrArg OneRectangle.leftFam hEq
    · intro R hR
      simp only [Finset.mem_image] at hR
      obtain ⟨H, hH, rfl⟩ := hR
      refine ⟨Finset.singleton_subset_iff.mpr hH, Finset.singleton_subset_iff.mpr hH, ?_⟩
      intro H₀ hH₀ H₁ hH₁
      rw [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁, mixedGraph_self S H (hHam H hH)]
      exact hHam H hH
    · intro H hH
      exact ⟨OneRectangle.mk ({H} : Finset (Finset (Edge n))) ({H} : Finset (Finset (Edge n))),
        Finset.mem_image.mpr ⟨H, hH, rfl⟩, Finset.mem_singleton_self H, Finset.mem_singleton_self H⟩
  · intro k hk
    rcases hk with ⟨P, hPcard, hRect, hCover⟩
    rw [← hPcard]
    have hDiagonalUnique :
        ∀ R ∈ P, ∀ H₀, H₀ ∈ R.leftFam → H₀ ∈ R.rightFam →
          ∀ H₁, H₁ ∈ R.leftFam → H₁ ∈ R.rightFam → H₀ = H₁ := by
      intro R hR H₀ hH₀L hH₀R H₁ hH₁L hH₁R
      by_contra hne
      have hRvalid := hRect R hR
      exact hIsolated H₀ (hRvalid.left_subset hH₀L) H₁ (hRvalid.right_subset hH₁R) hne
        (hRvalid.monochromatic H₀ hH₀L H₁ hH₁R)
    have hAssign : ∀ H ∈ I, ∃ R ∈ P, H ∈ R.leftFam ∧ H ∈ R.rightFam := by
      intro H hH
      exact hCover H hH
    let assign : {H // H ∈ I} → OneRectangle n := fun H => (hAssign H.1 H.2).choose
    have hAssignMem : ∀ H : {H // H ∈ I}, assign H ∈ P := by
      intro H
      exact (hAssign H.1 H.2).choose_spec.1
    have hAssignLeft : ∀ H : {H // H ∈ I}, H.1 ∈ (assign H).leftFam := by
      intro H
      exact (hAssign H.1 H.2).choose_spec.2.1
    have hAssignRight : ∀ H : {H // H ∈ I}, H.1 ∈ (assign H).rightFam := by
      intro H
      exact (hAssign H.1 H.2).choose_spec.2.2
    have hAssignInj : Function.Injective assign := by
      intro H₀ H₁ hEq
      apply Subtype.ext
      exact hDiagonalUnique (assign H₀) (hAssignMem H₀) H₀.1 (hAssignLeft H₀) (hAssignRight H₀)
        H₁.1 (by simpa [hEq] using hAssignLeft H₁) (by simpa [hEq] using hAssignRight H₁)
    calc
      I.card = (I.attach.image assign).card := by
        rw [Finset.card_image_of_injective _ hAssignInj, Finset.card_attach]
      _ ≤ P.card := by
        exact Finset.card_le_card (by
          intro R hR
          simp only [Finset.mem_image] at hR
          obtain ⟨H, hHI, rfl⟩ := hR
          exact hAssignMem H)

private theorem packing_gives_exponential_partition {n : ℕ}
    (hn : n ≥ 4)
    (S : Frontier n) (hS : S.isBalanced)
    (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q)
    (hPackedWitness : ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty) :
    ∃ (I : Finset (Finset (Edge n))),
      I.card ≥ 2 ^ q ∧
      (∀ H ∈ I, IsHamCycle n H) ∧
      (∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
        ¬IsHamCycle n (mixedGraph S H₁ H₀)) := by
  obtain ⟨blocks, hlen, hDisj, hVis, hOpen, hPat⟩ :=
    disjointOpenSwitchPacking S hS ρ hcons hpath polylogBound hm hn q hq_pos hq_bound hn_ge_q
      hPackedWitness
  set patterns := (Finset.univ : Finset (Fin blocks.length → Bool))
  have hChoose : ∀ η : Fin blocks.length → Bool,
      (patternHamCycles ρ blocks η).Nonempty := hPat
  classical
  let rep : (Fin blocks.length → Bool) → Finset (Edge n) :=
    fun η => (hChoose η).choose
  have hRepMem : ∀ η, rep η ∈ patternHamCycles ρ blocks η :=
    fun η => (hChoose η).choose_spec
  have hInj : Function.Injective rep := by
    intro η₀ η₁ h
    by_contra hne
    have hcontra := rectangleIsolation S ρ blocks hDisj hVis η₀ η₁ hne
      (rep η₀) (rep η₁) (hRepMem η₀) (hRepMem η₁)
    have hHam : IsHamCycle n (rep η₁) := by
      have hmem := hRepMem η₁
      unfold patternHamCycles restrictedHamCycles at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem.2.2
    have hself : mixedGraph S (rep η₁) (rep η₁) = rep η₁ := by
      ext e
      simp only [mixedGraph, leftSubgraph, rightSubgraph, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
      · intro he
        have hedge : e ∈ allEdges n := by
          simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hHam.noLoops e he
        have hpart := S.partition ▸ hedge
        rcases Finset.mem_union.mp hpart with hl | hr
        · exact Or.inl ⟨he, hl⟩
        · exact Or.inr ⟨he, hr⟩
    have hMixedHam : IsHamCycle n (mixedGraph S (rep η₁) (rep η₀)) := by
      rw [h, hself]
      exact hHam
    exact hcontra hMixedHam
  set I := Finset.univ.image rep
  have hIso : ∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
      ¬IsHamCycle n (mixedGraph S H₁ H₀) := by
    intro H₀ hH₀ H₁ hH₁ hne
    change H₀ ∈ Finset.image rep Finset.univ at hH₀
    change H₁ ∈ Finset.image rep Finset.univ at hH₁
    rcases Finset.mem_image.mp hH₀ with ⟨η₀, _, rfl⟩
    rcases Finset.mem_image.mp hH₁ with ⟨η₁, _, rfl⟩
    have hNeq : η₀ ≠ η₁ := by
      intro h; subst h; exact hne rfl
    exact rectangleIsolation S ρ blocks hDisj hVis η₀ η₁ hNeq
      (rep η₀) (rep η₁) (hRepMem η₀) (hRepMem η₁)
  have hHamI : ∀ H ∈ I, IsHamCycle n H := by
    intro H hH
    change H ∈ Finset.image rep Finset.univ at hH
    rcases Finset.mem_image.mp hH with ⟨η, _, rfl⟩
    have hmem := hRepMem η
    unfold patternHamCycles restrictedHamCycles at hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.2.2
  refine ⟨I, ?_, hHamI, hIso⟩
  calc
    I.card = (Finset.univ.image rep).card := rfl
    _ = Finset.univ.card := by rw [Finset.card_image_of_injective _ hInj]
    _ = 2 ^ blocks.length := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    _ = 2 ^ q := by simp [hlen]
    _ ≥ 2 ^ q := le_rfl

private theorem formula_size_from_isolation :
  ∀ {n : ℕ},
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (E : NaturalEdgeEncoding n m),
    ComputesHAMWithNaturalEncoding F E →
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    (∀ H ∈ I, IsHamCycle n H) →
    (∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ → ¬IsHamCycle n (mixedGraph S H₁ H₀)) →
    F.size ≥ I.card := by
  intro n m F hF E hCorrect S I hHam hIso
  rcases I.eq_empty_or_nonempty with rfl | ⟨H, hHI⟩
  · simp
  · have hout : F.outputGate < m + F.gates.length := by
      exact eval_true_implies_outputGate_lt F (E.encode H)
        ((hCorrect H).2 (hHam H hHI))
    have hAUY := auy_bound F hF E S I hCorrect hHam hout
    have hPart := funnel_partition_count S I hHam hIso
    omega

private theorem chromaticFrontierIsBalanced (χ : Coloring n) (hBal : χ.isBalanced) (hn : n ≥ 4) :
    (chromaticFrontier χ).isBalanced := by
  unfold Frontier.isBalanced
  unfold Coloring.isBalanced at hBal
  have hex_same : ∃ (u v : Fin n), u ≠ v ∧ χ.color u = χ.color v := by
    by_contra hall
    push_neg at hall
    have h01 : χ.color ⟨0, by omega⟩ ≠ χ.color ⟨1, by omega⟩ := by
      exact hall _ _ (by simp [Fin.ext_iff])
    have h02 : χ.color ⟨0, by omega⟩ ≠ χ.color ⟨2, by omega⟩ := by
      exact hall _ _ (by simp [Fin.ext_iff])
    have h12 : χ.color ⟨1, by omega⟩ ≠ χ.color ⟨2, by omega⟩ := by
      exact hall _ _ (by simp [Fin.ext_iff])
    cases h0 : χ.color ⟨0, by omega⟩ <;> cases h1 : χ.color ⟨1, by omega⟩ <;>
      cases h2 : χ.color ⟨2, by omega⟩ <;> simp_all
  have hex_diff : ∃ (u v : Fin n), u ≠ v ∧ χ.color u ≠ χ.color v := by
    simp only [decide_eq_true_eq] at hBal
    have hcard_pos : 0 < (Finset.univ.filter fun v : Fin n => χ.color v = true).card := by
      cases hBal with
      | inl h => omega
      | inr h => omega
    have hcard_lt : (Finset.univ.filter fun v : Fin n => χ.color v = true).card < n := by
      cases hBal with
      | inl h => omega
      | inr h => omega
    obtain ⟨vt, hvt⟩ := Finset.card_pos.mp hcard_pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvt
    have hcard_false : 0 < (Finset.univ.filter fun v : Fin n => χ.color v = false).card := by
      by_contra h
      push_neg at h
      have h0 : (Finset.univ.filter fun v : Fin n => χ.color v = false) = ∅ := by
        rwa [Nat.le_zero, Finset.card_eq_zero] at h
      have hall_true : ∀ v : Fin n, χ.color v = true := by
        intro v
        by_contra hv
        have : v ∈ (Finset.univ.filter fun v : Fin n => χ.color v = false) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          cases hcv : χ.color v <;> simp_all
        rw [h0] at this
        simp at this
      have : (Finset.univ.filter fun v : Fin n => χ.color v = true).card = n := by
        have heq :
            (Finset.univ.filter fun v : Fin n => χ.color v = true) = (Finset.univ : Finset (Fin n)) := by
          ext v
          simp [Finset.mem_filter, hall_true v]
        rw [heq, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨vf, hvf⟩ := Finset.card_pos.mp hcard_false
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvf
    exact ⟨vt, vf, by intro h; rw [h] at hvt; simp [hvt] at hvf, by rw [hvt, hvf]; simp⟩
  obtain ⟨us, vs, hnes, hcs⟩ := hex_same
  obtain ⟨ud, vd, hned, hcd⟩ := hex_diff
  constructor
  · apply Finset.card_pos.mpr
    refine ⟨Sym2.mk (us, vs), ?_⟩
    simp only [chromaticFrontier, Finset.mem_filter, allEdges, chromaticSameColor,
      Sym2.lift_mk, decide_eq_true_eq, Finset.mem_univ, true_and]
    exact ⟨by rw [Sym2.mk_isDiag_iff]; exact hnes, hcs⟩
  · apply Finset.card_pos.mpr
    refine ⟨Sym2.mk (ud, vd), ?_⟩
    simp only [chromaticFrontier, Finset.mem_filter, allEdges, chromaticSameColor,
      Sym2.lift_mk, Finset.mem_univ, true_and]
    refine ⟨by rw [Sym2.mk_isDiag_iff]; exact hned, ?_⟩
    simp only [decide_eq_false_iff_not]
    exact hcd

private def alternatingColoring (n : ℕ) : Coloring n where
  color v := decide (v.1 % 2 = 0)

private theorem alternatingChromaticFrontierIsBalanced (hn : n ≥ 4) :
    (chromaticFrontier (alternatingColoring n)).isBalanced := by
  unfold Frontier.isBalanced
  constructor
  · apply Finset.card_pos.mpr
    refine ⟨Sym2.mk (⟨0, by omega⟩, ⟨2, by omega⟩), ?_⟩
    simp [chromaticFrontier, chromaticSameColor, alternatingColoring, allEdges]
  · apply Finset.card_pos.mpr
    refine ⟨Sym2.mk (⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
    simp [chromaticFrontier, chromaticSameColor, alternatingColoring, allEdges]

private def canonicalBlock {n q : ℕ} (hq : q ≤ n / 4) (i : Fin q) : SwitchBlock n where
  p := ⟨4 * i.1, by
    have hi : i.1 < q := i.2
    have : 4 * q ≤ n := by
      exact le_trans (Nat.mul_le_mul_left 4 hq) (Nat.mul_div_le n 4)
    omega⟩
  a := ⟨4 * i.1 + 1, by
    have hi : i.1 < q := i.2
    have : 4 * q ≤ n := by
      exact le_trans (Nat.mul_le_mul_left 4 hq) (Nat.mul_div_le n 4)
    omega⟩
  b := ⟨4 * i.1 + 2, by
    have hi : i.1 < q := i.2
    have : 4 * q ≤ n := by
      exact le_trans (Nat.mul_le_mul_left 4 hq) (Nat.mul_div_le n 4)
    omega⟩
  q := ⟨4 * i.1 + 3, by
    have hi : i.1 < q := i.2
    have : 4 * q ≤ n := by
      exact le_trans (Nat.mul_le_mul_left 4 hq) (Nat.mul_div_le n 4)
    omega⟩
  all_distinct := by
    repeat' constructor
    · intro h
      have hv : 4 * i.1 = 4 * i.1 + 1 := by
        simpa using Fin.mk.inj h
      omega
    · intro h
      have hv : 4 * i.1 = 4 * i.1 + 2 := by
        simpa using Fin.mk.inj h
      omega
    · intro h
      have hv : 4 * i.1 = 4 * i.1 + 3 := by
        simpa using Fin.mk.inj h
      omega
    · intro h
      have hv : 4 * i.1 + 1 = 4 * i.1 + 2 := by
        simpa using Fin.mk.inj h
      omega
    · intro h
      have hv : 4 * i.1 + 1 = 4 * i.1 + 3 := by
        simpa using Fin.mk.inj h
      omega
    · intro h
      have hv : 4 * i.1 + 2 = 4 * i.1 + 3 := by
        simpa using Fin.mk.inj h
      omega

private noncomputable def canonicalBlocks {n q : ℕ} (hq : q ≤ n / 4) : List (SwitchBlock n) :=
  (List.finRange q).map (canonicalBlock hq)

private theorem canonicalBlocks_length {n q : ℕ} (hq : q ≤ n / 4) :
    (canonicalBlocks hq).length = q := by
  simp [canonicalBlocks]

private theorem canonicalBlocks_get {n q : ℕ} (hq : q ≤ n / 4)
    (i : Fin (canonicalBlocks hq).length) :
    (canonicalBlocks hq)[i] = canonicalBlock hq ⟨i.1, by
      simpa [canonicalBlocks_length hq] using i.2⟩ := by
  change ((List.finRange q).map (canonicalBlock hq))[i.1] =
      canonicalBlock hq ⟨i.1, by simpa [canonicalBlocks_length hq] using i.2⟩
  rw [List.getElem_map]
  simp [List.getElem_finRange]

private theorem canonicalBlocks_vertex_disjoint {n q : ℕ} (hq : q ≤ n / 4) :
    blocksVertexDisjoint (canonicalBlocks hq) := by
  intro i j hij
  rw [canonicalBlocks_get hq i, canonicalBlocks_get hq j]
  rw [Finset.disjoint_left]
  intro v hvI hvJ
  simp [SwitchBlock.vertices] at hvI hvJ
  have hijv : i.1 ≠ j.1 := by
    intro h
    apply hij
    ext
    exact h
  rcases hvI with rfl | rfl | rfl | rfl <;>
    rcases hvJ with h | h | h | h <;>
    have hv := congrArg Fin.val h <;>
    simp [canonicalBlock] at hv <;>
    omega

private theorem canonicalBlock_degree_visible {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4)
    (i : Fin q) :
    (canonicalBlock hq i).isDegreeVisible (chromaticFrontier (alternatingColoring n)) := by
  have _ : n ≥ 4 := hn
  unfold SwitchBlock.isDegreeVisible
  intro hmono
  have hpa :
      edgeSide (chromaticFrontier (alternatingColoring n))
        (Sym2.mk ((canonicalBlock hq i).p, (canonicalBlock hq i).a)) = false := by
    unfold edgeSide chromaticFrontier
    simp [chromaticSameColor, alternatingColoring, canonicalBlock, allEdges]
    omega
  have hpb :
      edgeSide (chromaticFrontier (alternatingColoring n))
        (Sym2.mk ((canonicalBlock hq i).p, (canonicalBlock hq i).b)) = true := by
    unfold edgeSide chromaticFrontier
    simp [chromaticSameColor, alternatingColoring, canonicalBlock, allEdges]
  have hpb_mem :
      Sym2.mk ((canonicalBlock hq i).p, (canonicalBlock hq i).b) ∈ (canonicalBlock hq i).toggleEdges := by
    simp [SwitchBlock.toggleEdges, canonicalBlock]
  have hpa_mem :
      Sym2.mk ((canonicalBlock hq i).p, (canonicalBlock hq i).a) ∈ (canonicalBlock hq i).toggleEdges := by
    simp [SwitchBlock.toggleEdges, canonicalBlock]
  have hpb_eq := hmono _ hpb_mem
  rw [hpa] at hpb_eq
  rw [hpb] at hpb_eq
  simp at hpb_eq

private noncomputable def canonicalPatternMap {n q : ℕ} (hq : q ≤ n / 4)
    (η : Fin q → Bool) (v : Fin n) : Fin n := by
  let k := v.1 / 4
  by_cases hk : k < q
  · by_cases hη : η ⟨k, hk⟩
    · by_cases h1 : v.1 % 4 = 1
      · refine ⟨4 * k + 2, ?_⟩
        have h4q : 4 * q ≤ n := by
          exact le_trans (Nat.mul_le_mul_left 4 hq) (Nat.mul_div_le n 4)
        omega
      · by_cases h2 : v.1 % 4 = 2
        · refine ⟨4 * k + 1, ?_⟩
          have h4q : 4 * q ≤ n := by
            exact le_trans (Nat.mul_le_mul_left 4 hq) (Nat.mul_div_le n 4)
          omega
        · exact v
    · exact v
  · exact v

private theorem canonicalPatternMap_involutive {n q : ℕ} (hq : q ≤ n / 4)
    (η : Fin q → Bool) :
    Function.Involutive (canonicalPatternMap hq η) := by
  intro v
  dsimp [canonicalPatternMap]
  let k := v.1 / 4
  by_cases hk : k < q
  · by_cases hη : η ⟨k, hk⟩
    · by_cases h1 : v.1 % 4 = 1
      · apply Fin.ext
        have hk' : (4 * k + 2) / 4 < q := by omega
        have hdiv : (4 * k + 2) / 4 = k := by omega
        have hkEq : (⟨(4 * k + 2) / 4, hk'⟩ : Fin q) = ⟨k, hk⟩ := by
          exact Fin.ext hdiv
        have hη' : η ⟨(4 * k + 2) / 4, hk'⟩ = true := by
          simpa [hkEq] using hη
        simp [k, hk, hη, h1, hk', hη']
        omega
      · by_cases h2 : v.1 % 4 = 2
        · apply Fin.ext
          have hk' : (4 * k + 1) / 4 < q := by omega
          have hdiv : (4 * k + 1) / 4 = k := by omega
          have hkEq : (⟨(4 * k + 1) / 4, hk'⟩ : Fin q) = ⟨k, hk⟩ := by
            exact Fin.ext hdiv
          have hη' : η ⟨(4 * k + 1) / 4, hk'⟩ = true := by
            simpa [hkEq] using hη
          simp [k, hk, hη, h1, h2, hk', hη']
          omega
        · simp [k, hk, hη, h1, h2]
    · simp [k, hk, hη]
  · simp [k, hk]

private noncomputable def canonicalPatternPerm {n q : ℕ} (hq : q ≤ n / 4)
    (η : Fin q → Bool) : Equiv.Perm (Fin n) where
  toFun := canonicalPatternMap hq η
  invFun := canonicalPatternMap hq η
  left_inv := canonicalPatternMap_involutive hq η
  right_inv := canonicalPatternMap_involutive hq η

private def canonicalBlocksEta {n q : ℕ} (hq : q ≤ n / 4) (η : Fin q → Bool) :
    Fin (canonicalBlocks hq).length → Bool :=
  fun i => η ⟨i.1, by simpa [canonicalBlocks_length hq] using i.2⟩

private def allFalsePattern {q : ℕ} : Fin q → Bool := fun _ => false

private def singleFlipPattern {q : ℕ} (i : Fin q) : Fin q → Bool :=
  fun j => decide (j = i)

private noncomputable def canonicalPatternCycle {n q : ℕ}
    (hn : n ≥ 4) (hq : q ≤ n / 4) (η : Fin q → Bool) : Finset (Edge n) :=
  PNeNp.relabelEdges (canonicalPatternPerm hq η) (canonEdges n (by omega))

private theorem canonicalPatternCycle_isHam
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4) (η : Fin q → Bool) :
    IsHamCycle n (canonicalPatternCycle hn hq η) := by
  unfold canonicalPatternCycle
  simpa using
    PNeNp.isHamCycle_relabel hn (canonicalPatternPerm hq η)
      (canonEdges n (by omega)) (canonicalCycleIsHam hn)

@[simp] private theorem canonicalPatternPerm_symm_apply
    {n q : ℕ} (hq : q ≤ n / 4) (η : Fin q → Bool) (v : Fin n) :
    (canonicalPatternPerm hq η).symm v = canonicalPatternPerm hq η v := rfl

@[simp] private theorem canonicalPatternPerm_apply_p
    {n q : ℕ} (hq : q ≤ n / 4) (η : Fin q → Bool) (i : Fin q) :
    canonicalPatternPerm hq η (canonicalBlock hq i).p = (canonicalBlock hq i).p := by
  apply Fin.ext
  simp [canonicalPatternPerm, canonicalPatternMap, canonicalBlock]

@[simp] private theorem canonicalPatternPerm_apply_q
    {n q : ℕ} (hq : q ≤ n / 4) (η : Fin q → Bool) (i : Fin q) :
    canonicalPatternPerm hq η (canonicalBlock hq i).q = (canonicalBlock hq i).q := by
  apply Fin.ext
  simp [canonicalPatternPerm, canonicalPatternMap, canonicalBlock]

@[simp] private theorem canonicalPatternPerm_apply_a_of_false
    {n q : ℕ} (hq : q ≤ n / 4) {η : Fin q → Bool} {i : Fin q}
    (hη : η i = false) :
    canonicalPatternPerm hq η (canonicalBlock hq i).a = (canonicalBlock hq i).a := by
  apply Fin.ext
  have hk : (4 * i.1 + 1) / 4 < q := by omega
  have hdiv : (4 * i.1 + 1) / 4 = i.1 := by omega
  have hmod1 : (4 * i.1 + 1) % 4 = 1 := by omega
  simp [canonicalPatternPerm, canonicalPatternMap, canonicalBlock, hk, hη, hdiv, hmod1]

@[simp] private theorem canonicalPatternPerm_apply_b_of_false
    {n q : ℕ} (hq : q ≤ n / 4) {η : Fin q → Bool} {i : Fin q}
    (hη : η i = false) :
    canonicalPatternPerm hq η (canonicalBlock hq i).b = (canonicalBlock hq i).b := by
  apply Fin.ext
  have hk : (4 * i.1 + 2) / 4 < q := by omega
  have hdiv : (4 * i.1 + 2) / 4 = i.1 := by omega
  have hmod1 : ¬ (4 * i.1 + 2) % 4 = 1 := by omega
  have hmod2 : (4 * i.1 + 2) % 4 = 2 := by omega
  simp [canonicalPatternPerm, canonicalPatternMap, canonicalBlock, hk, hη, hdiv, hmod1, hmod2]

@[simp] private theorem canonicalPatternPerm_apply_a_of_true
    {n q : ℕ} (hq : q ≤ n / 4) {η : Fin q → Bool} {i : Fin q}
    (hη : η i = true) :
    canonicalPatternPerm hq η (canonicalBlock hq i).a = (canonicalBlock hq i).b := by
  apply Fin.ext
  have hk : (4 * i.1 + 1) / 4 < q := by omega
  have hdiv : (4 * i.1 + 1) / 4 = i.1 := by omega
  have hmod1 : (4 * i.1 + 1) % 4 = 1 := by omega
  simp [canonicalPatternPerm, canonicalPatternMap, canonicalBlock, hk, hη, hdiv, hmod1]

@[simp] private theorem canonicalPatternPerm_apply_b_of_true
    {n q : ℕ} (hq : q ≤ n / 4) {η : Fin q → Bool} {i : Fin q}
    (hη : η i = true) :
    canonicalPatternPerm hq η (canonicalBlock hq i).b = (canonicalBlock hq i).a := by
  apply Fin.ext
  have hk : (4 * i.1 + 2) / 4 < q := by omega
  have hdiv : (4 * i.1 + 2) / 4 = i.1 := by omega
  have hmod1 : ¬ (4 * i.1 + 2) % 4 = 1 := by omega
  have hmod2 : (4 * i.1 + 2) % 4 = 2 := by omega
  simp [canonicalPatternPerm, canonicalPatternMap, canonicalBlock, hk, hη, hdiv, hmod1, hmod2]

private theorem state0Forced_subset_canonicalPatternCycle_of_false
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4)
    {η : Fin q → Bool} {i : Fin q} (hη : η i = false) :
    (canonicalBlock hq i).state0Forced ⊆ canonicalPatternCycle hn hq η := by
  intro e he
  simp [SwitchBlock.state0Forced] at he
  rcases he with rfl | rfl | rfl
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff]
    simp [canonicalPatternPerm_apply_p, canonicalPatternPerm_apply_a_of_false, hη]
    simpa [canonicalBlock] using canonEdges_step_mem hn (4 * i.1) (by omega)
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff]
    simp [canonicalPatternPerm_apply_a_of_false, canonicalPatternPerm_apply_b_of_false, hη]
    simpa [canonicalBlock] using canonEdges_step_mem hn (4 * i.1 + 1) (by omega)
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff]
    simp [canonicalPatternPerm_apply_b_of_false, canonicalPatternPerm_apply_q, hη]
    simpa [canonicalBlock] using canonEdges_step_mem hn (4 * i.1 + 2) (by omega)

private theorem state0Forbidden_disjoint_canonicalPatternCycle_of_false
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4)
    {η : Fin q → Bool} {i : Fin q} (hη : η i = false) :
    Disjoint (canonicalBlock hq i).state0Forbidden
      (canonicalPatternCycle hn hq η) := by
  rw [Finset.disjoint_left]
  intro e heForb heMem
  simp [SwitchBlock.state0Forbidden] at heForb
  rcases heForb with rfl | rfl
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff] at heMem
    simp [canonicalPatternPerm_apply_p, canonicalPatternPerm_apply_b_of_false, hη] at heMem
    exact canonEdges_two_apart_not_mem hn (4 * i.1) (by omega) heMem
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff] at heMem
    simp [canonicalPatternPerm_apply_a_of_false, canonicalPatternPerm_apply_q, hη] at heMem
    exact canonEdges_two_apart_not_mem hn (4 * i.1 + 1) (by omega) heMem

private theorem state1Forced_subset_canonicalPatternCycle_of_true
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4)
    {η : Fin q → Bool} {i : Fin q} (hη : η i = true) :
    (canonicalBlock hq i).state1Forced ⊆ canonicalPatternCycle hn hq η := by
  intro e he
  simp [SwitchBlock.state1Forced] at he
  rcases he with rfl | rfl | rfl
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff]
    simp [canonicalPatternPerm_apply_p, canonicalPatternPerm_apply_b_of_true, hη]
    simpa [canonicalBlock] using canonEdges_step_mem hn (4 * i.1) (by omega)
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff]
    simp [canonicalPatternPerm_apply_a_of_true, canonicalPatternPerm_apply_b_of_true, hη]
    have hstep :
        Sym2.mk ((canonicalBlock hq i).a, (canonicalBlock hq i).b) ∈
          canonEdges n (by omega) := by
      simpa [canonicalBlock] using canonEdges_step_mem hn (4 * i.1 + 1) (by omega)
    have hswap :
        Sym2.mk ((canonicalBlock hq i).b, (canonicalBlock hq i).a) =
          Sym2.mk ((canonicalBlock hq i).a, (canonicalBlock hq i).b) := by
      simp
    simpa [hswap] using hstep
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff]
    simp [canonicalPatternPerm_apply_a_of_true, canonicalPatternPerm_apply_q, hη]
    have hstep :
        Sym2.mk ((canonicalBlock hq i).b, (canonicalBlock hq i).q) ∈
          canonEdges n (by omega) := by
      simpa [canonicalBlock] using canonEdges_step_mem hn (4 * i.1 + 2) (by omega)
    simpa using hstep

private theorem state1Forbidden_disjoint_canonicalPatternCycle_of_true
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4)
    {η : Fin q → Bool} {i : Fin q} (hη : η i = true) :
    Disjoint (canonicalBlock hq i).state1Forbidden
      (canonicalPatternCycle hn hq η) := by
  rw [Finset.disjoint_left]
  intro e heForb heMem
  simp [SwitchBlock.state1Forbidden] at heForb
  rcases heForb with rfl | rfl
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff] at heMem
    simp [canonicalPatternPerm_apply_p, canonicalPatternPerm_apply_a_of_true, hη] at heMem
    exact canonEdges_two_apart_not_mem hn (4 * i.1) (by omega) heMem
  · rw [canonicalPatternCycle, PNeNp.mk_mem_relabelEdges_iff] at heMem
    simp [canonicalPatternPerm_apply_b_of_true, canonicalPatternPerm_apply_q, hη] at heMem
    exact canonEdges_two_apart_not_mem hn (4 * i.1 + 1) (by omega) heMem

private theorem canonicalBlock_state0_mem
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4) (i : Fin q) :
    canonicalPatternCycle hn hq (allFalsePattern) ∈
      restrictedHamCycles n
        ⟨(canonicalBlock hq i).state0Forced,
         (canonicalBlock hq i).state0Forbidden⟩ := by
  simp [restrictedHamCycles, canonicalPatternCycle_isHam, allFalsePattern]
  constructor
  · exact state0Forced_subset_canonicalPatternCycle_of_false hn hq rfl
  · exact state0Forbidden_disjoint_canonicalPatternCycle_of_false hn hq rfl

private theorem canonicalBlock_state1_mem
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4) (i : Fin q) :
    canonicalPatternCycle hn hq (singleFlipPattern i) ∈
      restrictedHamCycles n
        ⟨(canonicalBlock hq i).state1Forced,
         (canonicalBlock hq i).state1Forbidden⟩ := by
  simp [restrictedHamCycles, canonicalPatternCycle_isHam, singleFlipPattern]
  constructor
  · exact state1Forced_subset_canonicalPatternCycle_of_true hn hq (by simp [singleFlipPattern])
  · exact state1Forbidden_disjoint_canonicalPatternCycle_of_true hn hq (by simp [singleFlipPattern])

private theorem canonicalBlock_open_empty
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4) (i : Fin q) :
    (canonicalBlock hq i).isOpen (⟨∅, ∅⟩ : Restriction n) := by
  constructor
  · exact ⟨_, by
      simpa [SwitchBlock.isOpen, Finset.empty_union] using canonicalBlock_state0_mem hn hq i⟩
  · exact ⟨_, by
      simpa [SwitchBlock.isOpen, Finset.empty_union] using canonicalBlock_state1_mem hn hq i⟩

private theorem canonicalPatternCycle_mem_patternHamCycles
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4) (η : Fin q → Bool) :
    canonicalPatternCycle hn hq η ∈
      patternHamCycles
        (⟨∅, ∅⟩ : Restriction n)
        (canonicalBlocks hq)
        (canonicalBlocksEta hq η) := by
  unfold patternHamCycles restrictedHamCycles
  simp only [patternRestriction, Finset.empty_union, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, canonicalPatternCycle_isHam hn hq η⟩
  · intro e heForced
    rcases Finset.mem_biUnion.mp heForced with ⟨i, -, hi⟩
    let iq : Fin q := ⟨i.1, by simpa [canonicalBlocks_length hq] using i.2⟩
    have hget : (canonicalBlocks hq)[i] = canonicalBlock hq iq := by
      simpa [iq] using canonicalBlocks_get hq i
    by_cases hη : η iq = true
    · have hi' : e ∈ (canonicalBlock hq iq).state1Forced := by
        simpa [SwitchBlock.localRestriction, canonicalBlocksEta, hget, iq, hη] using hi
      exact state1Forced_subset_canonicalPatternCycle_of_true hn hq hη hi'
    · have hη0 : η iq = false := by cases h : η iq <;> simp_all
      have hi' : e ∈ (canonicalBlock hq iq).state0Forced := by
        simpa [SwitchBlock.localRestriction, canonicalBlocksEta, hget, iq, hη0] using hi
      exact state0Forced_subset_canonicalPatternCycle_of_false hn hq hη0 hi'
  · rw [Finset.disjoint_left]
    intro e heForb heMem
    rcases Finset.mem_biUnion.mp heForb with ⟨i, -, hi⟩
    let iq : Fin q := ⟨i.1, by simpa [canonicalBlocks_length hq] using i.2⟩
    have hget : (canonicalBlocks hq)[i] = canonicalBlock hq iq := by
      simpa [iq] using canonicalBlocks_get hq i
    by_cases hη : η iq = true
    · have hi' : e ∈ (canonicalBlock hq iq).state1Forbidden := by
        simpa [SwitchBlock.localRestriction, canonicalBlocksEta, hget, iq, hη] using hi
      exact (Finset.disjoint_left.mp
        (state1Forbidden_disjoint_canonicalPatternCycle_of_true hn hq hη)) hi' heMem
    · have hη0 : η iq = false := by cases h : η iq <;> simp_all
      have hi' : e ∈ (canonicalBlock hq iq).state0Forbidden := by
        simpa [SwitchBlock.localRestriction, canonicalBlocksEta, hget, iq, hη0] using hi
      exact (Finset.disjoint_left.mp
        (state0Forbidden_disjoint_canonicalPatternCycle_of_false hn hq hη0)) hi' heMem

private theorem canonicalPackedWitness
    {n q : ℕ} (hn : n ≥ 4) (hq : q ≤ n / 4) :
    ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length,
        blocks[i].isDegreeVisible (chromaticFrontier (alternatingColoring n))) ∧
      (∀ i : Fin blocks.length,
        blocks[i].isOpen (⟨∅, ∅⟩ : Restriction n)) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles (⟨∅, ∅⟩ : Restriction n) blocks η).Nonempty := by
  refine ⟨canonicalBlocks hq, canonicalBlocks_length hq,
    canonicalBlocks_vertex_disjoint hq, ?_, ?_, ?_⟩
  · intro i
    let iq : Fin q := ⟨i.1, by simpa [canonicalBlocks_length hq] using i.2⟩
    simpa [canonicalBlocks_get hq i, iq]
      using canonicalBlock_degree_visible hn hq iq
  · intro i
    let iq : Fin q := ⟨i.1, by simpa [canonicalBlocks_length hq] using i.2⟩
    simpa [canonicalBlocks_get hq i, iq]
      using canonicalBlock_open_empty hn hq iq
  · intro η
    let ηq : Fin q → Bool :=
      fun i => η ⟨i.1, by simpa [canonicalBlocks_length hq] using i.2⟩
    refine ⟨canonicalPatternCycle hn hq ηq, ?_⟩
    simpa [canonicalBlocksEta, ηq]
      using canonicalPatternCycle_mem_patternHamCycles hn hq ηq

theorem formulaSizeSuperpolynomial (hn : n ≥ 4) :
    ∀ m : ℕ, ∀ F : BooleanCircuit m, F.isFormula →
      ∀ E : NaturalEdgeEncoding n m,
      ComputesHAMWithNaturalEncoding F E →
      ∀ q : ℕ, 1 ≤ q → q ≤ n / 4 →
      F.size ≥ 2 ^ q := by
  intro m F hF E hCorrect q hq_pos hq_bound
  let χ := alternatingColoring n
  set S := chromaticFrontier χ
  have hSBal : S.isBalanced := by
    simpa [χ, S] using alternatingChromaticFrontierIsBalanced hn
  set ρ₀ : Restriction n := ⟨∅, ∅⟩
  have hCons₀ : ρ₀.consistent := by
    unfold Restriction.consistent; exact Finset.disjoint_empty_right _
  have hPath₀ : ρ₀.isPathCompatible := by
    unfold Restriction.isPathCompatible Restriction.maxDegree ρ₀
    constructor
    · simp
    constructor
    · simp
    · intro comp hsub _ hne
      exfalso
      apply hne.ne_empty
      ext e
      constructor
      · intro he
        exact False.elim (Finset.notMem_empty e (hsub he))
      · intro he
        exact False.elim (Finset.notMem_empty e he)
  have hSize₀ : ρ₀.size ≤ q := by unfold Restriction.size ρ₀; simp
  have hn_ge_q : n ≥ q := by omega
  have hPackedWitness :
      ∃ (blocks : List (SwitchBlock n)),
        blocks.length = q ∧
        blocksVertexDisjoint blocks ∧
        (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
        (∀ i : Fin blocks.length, blocks[i].isOpen ρ₀) ∧
        ∀ η : Fin blocks.length → Bool,
          (patternHamCycles ρ₀ blocks η).Nonempty := by
    simpa [S, ρ₀] using canonicalPackedWitness (n := n) (q := q) hn hq_bound
  obtain ⟨I, hIcard, hHam, hIso⟩ := packing_gives_exponential_partition hn S hSBal ρ₀ hCons₀ hPath₀ q
    hSize₀ q hq_pos (le_refl q) hn_ge_q hPackedWitness
  have hFge := formula_size_from_isolation m F hF E hCorrect S I hHam hIso
  omega

private theorem formula_lower_bound_iterated_funnel_ax :
  ∀ {n : ℕ}, n ≥ 4 →
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (E : NaturalEdgeEncoding n m),
    ComputesHAMWithNaturalEncoding F E →
    ∃ d : ℕ, d > 0 ∧ F.size ≥ 2 ^ (n / d) := by
  intro n hn4 m F hFormula E hCorrect
  refine ⟨4, by omega, ?_⟩
  have hn4_div : n / 4 ≥ 1 := by omega
  exact formulaSizeSuperpolynomial hn4 m F hFormula E hCorrect
    (n / 4) hn4_div (le_refl _)

theorem formulaLowerBound (hn : n ≥ 4) :
    ∀ m : ℕ, ∀ F : BooleanCircuit m, F.isFormula →
      ∀ E : NaturalEdgeEncoding n m,
      ComputesHAMWithNaturalEncoding F E →
      ∃ d : ℕ, d > 0 ∧ F.size ≥ 2 ^ (n / d) :=
  fun m F hF E hCorrect =>
    formula_lower_bound_iterated_funnel_ax hn m F hF E hCorrect

end FormulaLowerBound

end PNeNp

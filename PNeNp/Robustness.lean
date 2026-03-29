import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Switch
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.ZMod.Basic

open Finset

namespace PNeNp

section CanonicalCycle

variable {n : ℕ}

private def cycNext (hn : n ≥ 1) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩

private def cycPrev (hn : n ≥ 1) (i : Fin n) : Fin n :=
  ⟨(i.val + (n - 1)) % n, Nat.mod_lt _ (by omega)⟩

private lemma cycNext_val (hn : n ≥ 1) (i : Fin n) :
    (cycNext hn i).val = (i.val + 1) % n := rfl

private lemma cycPrev_val (hn : n ≥ 1) (i : Fin n) :
    (cycPrev hn i).val = (i.val + (n - 1)) % n := rfl

private lemma cycNext_ne (hn : n ≥ 3) (i : Fin n) : cycNext (by omega) i ≠ i := by
  intro h; have := congr_arg Fin.val h; rw [cycNext_val] at this
  by_cases h : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h] at this; omega
  · rw [show i.val + 1 = n from by omega, Nat.mod_self] at this; omega

private lemma cycNext_cycPrev (hn : n ≥ 3) (i : Fin n) :
    cycNext (by omega) (cycPrev (by omega) i) = i := by
  apply Fin.ext; rw [cycNext_val, cycPrev_val]
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl n), ← Nat.add_mod,
      show i.val + (n - 1) + 1 = i.val + n * 1 from by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

private lemma cycPrev_cycNext (hn : n ≥ 3) (i : Fin n) :
    cycPrev (by omega) (cycNext (by omega) i) = i := by
  apply Fin.ext; rw [cycPrev_val, cycNext_val]
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl n), ← Nat.add_mod,
      show i.val + 1 + (n - 1) = i.val + n * 1 from by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

private lemma cycNext_ne_cycPrev (hn : n ≥ 4) (i : Fin n) :
    cycNext (by omega) i ≠ cycPrev (by omega) i := by
  intro h; have hv := congr_arg Fin.val h; rw [cycNext_val, cycPrev_val] at hv
  by_cases h1 : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : i.val = 0
    · rw [h2] at hv
      rw [show 0 + (n - 1) = n - 1 by omega,
        Nat.mod_eq_of_lt (by omega : n - 1 < n)] at hv
      omega
    · rw [show i.val + (n - 1) = (i.val - 1) + n * 1 from by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at hv; omega
  · push_neg at h1
    have : i.val + 1 = n := by omega
    rw [this, Nat.mod_self] at hv
    rw [show i.val + (n - 1) = 2 * n - 2 from by omega] at hv
    rw [show 2 * n - 2 = (n - 2) + n * 1 from by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : n - 2 < n)] at hv; omega

noncomputable def canonEdges (n : ℕ) (hn : n ≥ 3) : Finset (Edge n) :=
  Finset.univ.image fun (i : Fin n) => Sym2.mk (i, cycNext (by omega) i)

private lemma canonEdges_mem (hn : n ≥ 3) (i : Fin n) :
    Sym2.mk (i, cycNext (by omega) i) ∈ canonEdges n hn :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private lemma canonEdges_pred_mem (hn : n ≥ 3) (i : Fin n) :
    Sym2.mk (cycPrev (by omega) i, i) ∈ canonEdges n hn := by
  have h := canonEdges_mem hn (cycPrev (by omega) i)
  rwa [cycNext_cycPrev (by omega)] at h

private lemma canonEdges_mem_iff (hn : n ≥ 3) (e : Edge n) :
    e ∈ canonEdges n hn ↔
    ∃ i : Fin n, e = Sym2.mk (i, cycNext (by omega) i) := by
  constructor
  · exact fun he => (Finset.mem_image.mp he).imp fun i hi => hi.2.symm
  · rintro ⟨i, hi⟩
    rw [hi]
    exact canonEdges_mem hn i

private lemma canonEdges_noLoops (hn : n ≥ 3) :
    ∀ e ∈ canonEdges n hn, ¬e.IsDiag := by
  intro e he; rw [canonEdges_mem_iff] at he; obtain ⟨i, rfl⟩ := he
  rw [Sym2.mk_isDiag_iff]; exact (cycNext_ne hn i).symm

private lemma canonEdges_spanning (hn : n ≥ 3) :
    ∀ v : Fin n, ∃ e ∈ canonEdges n hn, v ∈ e :=
  fun v => ⟨_, canonEdges_mem hn v, Sym2.mem_mk_left _ _⟩

private lemma canon_filter_eq (hn : n ≥ 4) (v : Fin n) :
    (canonEdges n (by omega : n ≥ 3)).filter (v ∈ ·) =
    {Sym2.mk (v, cycNext (by omega) v), Sym2.mk (cycPrev (by omega) v, v)} := by
  ext e; simp only [mem_filter, mem_insert, mem_singleton]; constructor
  · intro ⟨he, hv⟩; rw [canonEdges_mem_iff] at he; obtain ⟨i, rfl⟩ := he
    simp only [Sym2.mem_iff] at hv; rcases hv with rfl | hvi
    · left; rfl
    · right
      have hi : i = cycPrev (by omega) v := by
        have hvi' : v = cycNext (by omega) i := hvi
        rw [hvi', cycPrev_cycNext (show n ≥ 3 by omega)]
      rw [hi, hvi, cycNext_cycPrev (show n ≥ 3 by omega)]
  · intro h; rcases h with rfl | rfl
    · exact ⟨canonEdges_mem _ v, Sym2.mem_mk_left _ _⟩
    · exact ⟨canonEdges_pred_mem _ v, Sym2.mem_mk_right _ _⟩

private lemma cycPrev_ne (hn : n ≥ 3) (i : Fin n) : cycPrev (by omega) i ≠ i := by
  intro h
  have hnext := congrArg (cycNext (by omega)) h
  have hnext' : i = cycNext (by omega) i := by
    simpa [cycNext_cycPrev (show n ≥ 3 by omega)] using hnext
  exact cycNext_ne (show n ≥ 3 by omega) i hnext'.symm

private lemma canon_pair_ne (hn : n ≥ 4) (v : Fin n) :
    Sym2.mk (v, cycNext (by omega) v) ≠ Sym2.mk (cycPrev (by omega) v, v) := by
  intro h; have := Sym2.eq_iff.mp h
  rcases this with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact cycPrev_ne (show n ≥ 3 by omega) v h1.symm
  · exact cycNext_ne_cycPrev hn v (h1 ▸ h2)

private lemma canon_twoRegular (hn : n ≥ 4) :
    ∀ v : Fin n, vertexDegreeIn n (canonEdges n (by omega)) v = 2 := by
  intro v; unfold vertexDegreeIn
  rw [canon_filter_eq hn v]; exact Finset.card_pair (canon_pair_ne hn v)

private lemma canon_adj (hn : n ≥ 3) (i : Fin n) :
    (edgeSetToGraph n (canonEdges n hn)).Adj i (cycNext (by omega) i) :=
  ⟨(cycNext_ne hn i).symm, canonEdges_mem hn i⟩

private lemma canon_reachable (hn : n ≥ 3) (u v : Fin n) :
    (edgeSetToGraph n (canonEdges n hn)).Reachable u v := by
  have h0 : 0 < n := by omega
  suffices h : ∀ k : ℕ, ∀ hk : k < n,
      (edgeSetToGraph n (canonEdges n hn)).Reachable ⟨0, h0⟩ ⟨k, hk⟩ by
    exact (h u.val u.isLt).symm.trans (h v.val v.isLt)
  intro k hk
  induction k with
  | zero =>
      exact SimpleGraph.Reachable.refl _
  | succ k ih =>
      have hk' : k < n := by omega
      have ih' := ih hk'
      have step : (edgeSetToGraph n (canonEdges n hn)).Adj
          ⟨k, hk'⟩ ⟨k + 1, hk⟩ := by
        constructor
        · intro h
          have : k = k + 1 := congrArg Fin.val h
          omega
        · have hmem := canonEdges_mem hn ⟨k, hk'⟩
          have hnext_eq : cycNext (by omega) ⟨k, hk'⟩ = ⟨k + 1, hk⟩ := by
            apply Fin.ext
            simp [cycNext_val, Nat.mod_eq_of_lt hk]
          simpa [hnext_eq] using hmem
      exact ih'.trans step.reachable

private lemma canon_connected (hn : n ≥ 3) :
    IsConnectedEdgeSet n (canonEdges n hn) := by
  unfold IsConnectedEdgeSet
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact ⟨fun u v => canon_reachable hn u v⟩

theorem canonicalCycleIsHam (hn : n ≥ 4) :
    IsHamCycle n (canonEdges n (by omega)) where
  twoRegular := canon_twoRegular hn
  connected := canon_connected (by omega)
  noLoops := canonEdges_noLoops (by omega)
  spanning := canonEdges_spanning (by omega)

end CanonicalCycle

section EmptyRestriction

variable {n : ℕ}

private def emptyRestriction (n : ℕ) : Restriction n := ⟨∅, ∅⟩

theorem restrictedHamCycles_nonempty_of_ge4 (hn : n ≥ 4) :
    (restrictedHamCycles n (emptyRestriction n)).Nonempty := by
  refine ⟨canonEdges n (by omega), ?_⟩
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and,
    emptyRestriction, Finset.empty_subset, Finset.disjoint_empty_left, true_and]
  exact canonicalCycleIsHam hn

end EmptyRestriction

section Relabeling

variable {n : ℕ}

noncomputable def relabelEdges (σ : Equiv.Perm (Fin n)) (H : Finset (Edge n)) :
    Finset (Edge n) :=
  H.map (Function.Embedding.sym2Map σ.toEmbedding)

private lemma mem_relabelEdge_iff (σ : Equiv.Perm (Fin n)) (e : Edge n) (v : Fin n) :
    v ∈ Sym2.map σ e ↔ σ.symm v ∈ e := by
  constructor
  · intro hv
    rcases Sym2.mem_map.mp hv with ⟨w, hw, hwv⟩
    have hsymm : σ.symm v = w := by
      simpa using (congrArg σ.symm hwv).symm
    simpa [hsymm] using hw
  · intro hv
    exact Sym2.mem_map.mpr ⟨σ.symm v, hv, by simp⟩

private lemma relabelEdges_filter_eq (σ : Equiv.Perm (Fin n)) (H : Finset (Edge n)) (v : Fin n) :
    (relabelEdges σ H).filter (v ∈ ·) =
      (H.filter fun e => σ.symm v ∈ e).map (Function.Embedding.sym2Map σ.toEmbedding) := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_filter.mp he with ⟨hemap, hv⟩
    rcases Finset.mem_map.mp hemap with ⟨a, ha, hae⟩
    refine Finset.mem_map.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩, hae⟩
    have hae' : Sym2.map σ a = e := by
      simpa [Function.Embedding.sym2Map] using hae
    have hv' : v ∈ Sym2.map σ a := by
      rw [hae']
      exact hv
    exact (mem_relabelEdge_iff σ a v).mp hv'
  · intro he
    rcases Finset.mem_map.mp he with ⟨a, ha, hae⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨a, (Finset.mem_filter.mp ha).1, hae⟩, ?_⟩
    have hv' : σ.symm v ∈ a := (Finset.mem_filter.mp ha).2
    have : v ∈ Sym2.map σ a := (mem_relabelEdge_iff σ a v).2 hv'
    have hae' : Sym2.map σ a = e := by
      simpa [Function.Embedding.sym2Map] using hae
    rw [hae'] at this
    exact this

private lemma relabel_adj {n : ℕ} (σ : Equiv.Perm (Fin n)) (H : Finset (Edge n))
    {u v : Fin n} (hadj : (edgeSetToGraph n H).Adj u v) :
    (edgeSetToGraph n (relabelEdges σ H)).Adj (σ u) (σ v) := by
  rcases hadj with ⟨huv, huv_mem⟩
  refine ⟨by intro h; exact huv (σ.injective h), ?_⟩
  exact Finset.mem_map.mpr ⟨Sym2.mk (u, v), huv_mem, by simp [Sym2.map_mk]⟩

private lemma relabel_reachable {n : ℕ} (σ : Equiv.Perm (Fin n)) (H : Finset (Edge n))
    {u v : Fin n} (hreach : (edgeSetToGraph n H).Reachable u v) :
    (edgeSetToGraph n (relabelEdges σ H)).Reachable (σ u) (σ v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach ⊢
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hprev hadj ih =>
      exact Relation.ReflTransGen.tail ih (relabel_adj σ H hadj)

theorem isHamCycle_relabel (_hn : n ≥ 4) (σ : Equiv.Perm (Fin n))
    (H : Finset (Edge n)) (hH : IsHamCycle n H) :
    IsHamCycle n (relabelEdges σ H) where
  twoRegular := by
    intro v
    unfold vertexDegreeIn
    rw [relabelEdges_filter_eq σ H v, Finset.card_map]
    simpa using hH.twoRegular (σ.symm v)
  connected := by
    have hconn := hH.connected
    unfold IsConnectedEdgeSet at hconn ⊢
    haveI := hconn.nonempty.map σ
    exact ⟨fun v w => by
      simpa using relabel_reachable σ H (u := σ.symm v) (v := σ.symm w)
        (hconn.preconnected (σ.symm v) (σ.symm w))⟩
  noLoops := by
    intro e he
    rcases Finset.mem_map.mp he with ⟨e₀, he₀, rfl⟩
    exact mt (Sym2.isDiag_map σ.injective).mp (hH.noLoops e₀ he₀)
  spanning := by
    intro v
    obtain ⟨e, he, hv⟩ := hH.spanning (σ.symm v)
    refine ⟨Sym2.map σ e, Finset.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
    exact (mem_relabelEdge_iff σ e v).2 hv

theorem mk_mem_relabelEdges_iff (σ : Equiv.Perm (Fin n)) (H : Finset (Edge n))
    (u v : Fin n) :
    Sym2.mk (u, v) ∈ relabelEdges σ H ↔ Sym2.mk (σ.symm u, σ.symm v) ∈ H := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨e, he, hmap⟩
    have heq : Sym2.mk (σ.symm u, σ.symm v) = e := by
      apply (Function.Embedding.sym2Map σ.toEmbedding).injective
      simpa [Sym2.map_mk] using hmap.symm
    simpa [heq] using he
  · intro h
    refine Finset.mem_map.mpr ?_
    refine ⟨Sym2.mk (σ.symm u, σ.symm v), h, ?_⟩
    simp [Sym2.map_mk]

theorem canonEdges_step_mem (hn : n ≥ 4) (k : ℕ) (hk : k + 1 < n) :
    Sym2.mk (⟨k, by omega⟩, ⟨k + 1, hk⟩) ∈ canonEdges n (by omega) := by
  have hmem := canonEdges_mem (n := n) (by omega) ⟨k, by omega⟩
  have hnext : cycNext (by omega) ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by
    apply Fin.ext
    simp [cycNext_val, Nat.mod_eq_of_lt hk]
  simpa [hnext] using hmem

theorem canonEdges_wrap_mem (hn : n ≥ 4) :
    Sym2.mk (⟨n - 1, Nat.sub_lt (by omega) (by omega)⟩,
             (⟨0, by omega⟩ : Fin n)) ∈ canonEdges n (by omega) := by
  have hmem := canonEdges_mem (n := n) (by omega) ⟨n - 1, Nat.sub_lt (by omega) (by omega)⟩
  have hnext : cycNext (by omega) ⟨n - 1, Nat.sub_lt (by omega) (by omega)⟩ =
      (⟨0, by omega⟩ : Fin n) := by
    apply Fin.ext
    simp only [cycNext_val, Fin.val_mk]
    have hnn : n - 1 + 1 = n := by omega
    rw [hnn, Nat.mod_self]
  rw [hnext] at hmem
  exact hmem

theorem canonEdges_mem_cases (hn : n ≥ 4) (x y : Fin n)
    (hmem : Sym2.mk (x, y) ∈ canonEdges n (by omega)) :
    (∃ k : ℕ, ∃ hk : k + 1 < n,
      Sym2.mk (x, y) = Sym2.mk (⟨k, by omega⟩, ⟨k + 1, hk⟩)) ∨
    Sym2.mk (x, y) = Sym2.mk (⟨n - 1, Nat.sub_lt (by omega) (by omega)⟩,
                               (⟨0, by omega⟩ : Fin n)) := by
  rw [canonEdges_mem_iff (hn := by omega)] at hmem
  obtain ⟨i, hi⟩ := hmem
  by_cases hlt : i.val + 1 < n
  · left
    refine ⟨i.val, hlt, ?_⟩
    have hnext : cycNext (by omega) i = ⟨i.val + 1, hlt⟩ := by
      apply Fin.ext
      simp [cycNext_val, Nat.mod_eq_of_lt hlt]
    rw [hi, hnext]
  · right
    have heq : i.val = n - 1 := by omega
    have hnext : cycNext (by omega) i = (⟨0, by omega⟩ : Fin n) := by
      apply Fin.ext
      simp [cycNext_val]
      have : i.val + 1 = n := by omega
      rw [this, Nat.mod_self]
    rw [hi, hnext]
    rw [Sym2.eq_iff]
    left
    exact ⟨Fin.ext heq, rfl⟩

theorem canonEdges_two_apart_not_mem (hn : n ≥ 4) (k : ℕ) (hk : k + 2 < n) :
    Sym2.mk (⟨k, by omega⟩, ⟨k + 2, hk⟩) ∉ canonEdges n (by omega) := by
  intro hmem
  rw [canonEdges_mem_iff (n := n) (hn := by omega)] at hmem
  rcases hmem with ⟨i, hi⟩
  have hcases := Sym2.eq_iff.mp hi
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hi1 : i.1 = k := by simpa using (congrArg Fin.val h1).symm
    have hi2 : (cycNext (by omega) i).1 = k + 2 := by simpa using (congrArg Fin.val h2).symm
    have hi2' : k + 1 = k + 2 := by
      simpa [hi1, cycNext_val, Nat.mod_eq_of_lt (by omega : k + 1 < n)] using hi2
    omega
  · have hi1 : i.1 = k + 2 := by simpa using (congrArg Fin.val h2).symm
    have hi2 : (cycNext (by omega) i).1 = k := by simpa using (congrArg Fin.val h1).symm
    by_cases hk3 : k + 3 < n
    · have hi2' : k + 3 = k := by
        simpa [hi1, cycNext_val, Nat.mod_eq_of_lt hk3] using hi2
      omega
    · have hk3eq : k + 3 = n := by omega
      have hi2' : 0 = k := by
        simpa [hi1, cycNext_val, hk3eq] using hi2
      omega

end Relabeling

section Robustness

variable {n : ℕ}

open Classical in
private lemma restrictedHamCycles_monotone_absent (_hn : n ≥ 4)
    (ρ : Restriction n) (e : Edge n)
    (_hne : (restrictedHamCycles n ρ).Nonempty)
    (_hsize : 2 * ρ.size + 4 ≤ n)
    (_he_nin : e ∉ ρ.forcedPresent) (_he_nin_abs : e ∉ ρ.forcedAbsent) :
    (∃ H ∈ restrictedHamCycles n ρ, e ∉ H) →
    (restrictedHamCycles n ⟨ρ.forcedPresent, ρ.forcedAbsent ∪ {e}⟩).Nonempty := by
  intro havoid
  rcases havoid with ⟨H, hH, heH⟩
  refine ⟨H, ?_⟩
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and] at hH ⊢
  refine ⟨hH.1, ?_⟩
  refine ⟨?_, hH.2.2⟩
  rw [Finset.disjoint_union_left]
  exact ⟨hH.2.1, Finset.disjoint_singleton_left.mpr heH⟩

open Classical in
private lemma restrictedHamCycles_monotone_present (_hn : n ≥ 4)
    (ρ : Restriction n) (e : Edge n)
    (_hne : (restrictedHamCycles n ρ).Nonempty)
    (_hpath : ρ.isPathCompatible)
    (_hpath_ext : (⟨ρ.forcedPresent ∪ {e}, ρ.forcedAbsent⟩ : Restriction n).isPathCompatible)
    (_hsize : 2 * ρ.size + 4 ≤ n)
    (_he_nin : e ∉ ρ.forcedPresent) (_he_nin_abs : e ∉ ρ.forcedAbsent) :
    (∃ H ∈ restrictedHamCycles n ρ, e ∈ H) →
    (restrictedHamCycles n ⟨ρ.forcedPresent ∪ {e}, ρ.forcedAbsent⟩).Nonempty := by
  intro hinclude
  rcases hinclude with ⟨H, hH, heH⟩
  refine ⟨H, ?_⟩
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and] at hH ⊢
  refine ⟨?_, hH.2.1, hH.2.2⟩
  intro f hf
  simp only [Finset.mem_union, Finset.mem_singleton] at hf
  rcases hf with hf | rfl
  · exact hH.1 hf
  · exact heH

theorem restrictedHamCycles_nonempty_of_realize (hn : n ≥ 4)
    (ρ : Restriction n) (_hcons : ρ.consistent) (_hpath : ρ.isPathCompatible)
    (_hsize : 2 * ρ.size + 4 ≤ n)
    (hrealize : ∃ σ : Equiv.Perm (Fin n),
      ρ.forcedPresent ⊆ relabelEdges σ (canonEdges n (by omega)) ∧
      Disjoint ρ.forcedAbsent (relabelEdges σ (canonEdges n (by omega)))) :
    (restrictedHamCycles n ρ).Nonempty := by
  rcases hrealize with ⟨σ, hpresent, habsent⟩
  refine ⟨relabelEdges σ (canonEdges n (by omega)), ?_⟩
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hpresent, habsent, isHamCycle_relabel hn σ _ (canonicalCycleIsHam hn)⟩

section RobustnessArithmetic

private lemma forcedPresent_card_le_size (ρ : Restriction n) :
    ρ.forcedPresent.card ≤ ρ.size := by
  unfold Restriction.size
  omega

private lemma forcedAbsent_card_le_size (ρ : Restriction n) :
    ρ.forcedAbsent.card ≤ ρ.size := by
  unfold Restriction.size
  omega

private lemma contracted_minus_one_gt_twice_absent
    (ρ : Restriction n)
    (hsize : 2 * ρ.size + 4 ≤ n) :
    n - ρ.forcedPresent.card - 1 > 2 * ρ.forcedAbsent.card := by
  unfold Restriction.size at hsize
  omega

private lemma contracted_minus_one_pos
    (ρ : Restriction n)
    (hsize : 2 * ρ.size + 4 ≤ n) :
    0 < n - ρ.forcedPresent.card - 1 := by
  have h := contracted_minus_one_gt_twice_absent (n := n) ρ hsize
  omega

private lemma contracted_ge_half_plus_two
    (ρ : Restriction n)
    (hsize : 2 * ρ.size + 4 ≤ n) :
    n / 2 + 2 ≤ n - ρ.forcedPresent.card := by
  have hp : ρ.forcedPresent.card ≤ ρ.size := forcedPresent_card_le_size ρ
  unfold Restriction.size at hsize
  omega

private lemma half_minus_one_le_contracted_minus_two
    (ρ : Restriction n)
    (hsize : 2 * ρ.size + 4 ≤ n) :
    n / 2 - 1 ≤ n - ρ.forcedPresent.card - 2 := by
  have h := contracted_ge_half_plus_two (n := n) ρ hsize
  omega

private lemma survival_margin_pos
    (ρ : Restriction n)
    (hsize : 2 * ρ.size + 4 ≤ n) :
    0 < (n - ρ.forcedPresent.card - 1) - 2 * ρ.forcedAbsent.card := by
  have h := contracted_minus_one_gt_twice_absent (n := n) ρ hsize
  omega

end RobustnessArithmetic

end Robustness

end PNeNp

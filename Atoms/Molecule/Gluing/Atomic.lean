import Atoms.Molecule.Gluing.BoundaryIso

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}} {t : P} {t' : Q}

theorem mem_bdryFull_iff_ne (ht : IsTop t) {x : P} : x ∈ P.bdryFull ⊤ ↔ x ≠ t := by
  have hT : (⊤ : LowerSet P) = .Iic t := SetLike.ext fun y => iff_of_true LowerSet.mem_top (ht y)
  rw [hT, bdryFull, ← SetLike.mem_coe, coe_bdry_Iic_sup, Set.mem_Iio]
  exact ⟨ne_of_lt, lt_of_le_of_ne (ht x)⟩

theorem orient_eq_iff_mem_bdry (ht : IsTop t) {y : P} (hy : y ⋖ t) (α : Bool) :
    P.orient hy = α ↔ y ∈ P.bdry ⊤ α := by
  have hT : (⊤ : LowerSet P) = .Iic t := SetLike.ext fun z => iff_of_true LowerSet.mem_top (ht z)
  rw [hT]
  refine ⟨fun h => h ▸ mem_bdry_Iic_of_covBy hy, fun h => ?_⟩
  obtain ⟨h', ho⟩ := mem_faces_of_mem_bdry_Iic h (Nat.covBy_iff_add_one_eq.1 (hy.grade ℕ))
  exact ho

section Extend

variable [DecidablePred (· ∈ P.bdryFull ⊤)]

def extendTop (t' : Q) (f : P.restrict (P.bdryFull ⊤) → Q.restrict (Q.bdryFull ⊤))
    (x : P) : Q :=
  if h : x ∈ P.bdryFull ⊤ then (f ⟨x, h⟩ : Q) else t'

theorem extendTop_of_mem (f : P.restrict (P.bdryFull ⊤) → Q.restrict (Q.bdryFull ⊤)) {x : P}
    (h : x ∈ P.bdryFull ⊤) : extendTop t' f x = f ⟨x, h⟩ :=
  dif_pos h

theorem extendTop_of_notMem (f : P.restrict (P.bdryFull ⊤) → Q.restrict (Q.bdryFull ⊤))
    {x : P} (h : x ∉ P.bdryFull ⊤) : extendTop t' f x = t' :=
  dif_neg h

variable [DecidablePred (· ∈ Q.bdryFull ⊤)] (ht : IsTop t) (ht' : IsTop t')
  (ψ : P.restrict (P.bdryFull ⊤) ≅ Q.restrict (Q.bdryFull ⊤))
include ht ht'

def extendTopOrderIso : P ≃o Q where
  toFun := extendTop t' ψ.hom
  invFun := extendTop t ψ.inv
  left_inv x := by
    by_cases hx : x ∈ P.bdryFull ⊤
    · rw [extendTop_of_mem _ hx, extendTop_of_mem _ (ψ.hom ⟨x, hx⟩).2]
      exact congrArg Subtype.val (ψ.hom_inv_id_apply ⟨x, hx⟩)
    · rw [extendTop_of_notMem _ hx,
        extendTop_of_notMem _ fun h => (mem_bdryFull_iff_ne ht').1 h rfl]
      exact (not_not.1 ((mem_bdryFull_iff_ne ht).not.1 hx)).symm
  right_inv y := by
    by_cases hy : y ∈ Q.bdryFull ⊤
    · rw [extendTop_of_mem _ hy, extendTop_of_mem _ (ψ.inv ⟨y, hy⟩).2]
      exact congrArg Subtype.val (ψ.inv_hom_id_apply ⟨y, hy⟩)
    · rw [extendTop_of_notMem _ hy, extendTop_of_notMem _ fun h => (mem_bdryFull_iff_ne ht).1 h rfl]
      exact (not_not.1 ((mem_bdryFull_iff_ne ht').not.1 hy)).symm
  map_rel_iff' {x y} := by
    have htop {z : Q} (hz : z ∈ Q.bdryFull ⊤) : ¬ t' ≤ z := fun h =>
      (mem_bdryFull_iff_ne ht').1 hz (le_antisymm (ht' z) h)
    have htop' {z : P} (hz : z ∈ P.bdryFull ⊤) : ¬ t ≤ z := fun h =>
      (mem_bdryFull_iff_ne ht).1 hz (le_antisymm (ht z) h)
    have heq {z : P} (hz : z ∉ P.bdryFull ⊤) : z = t :=
      not_not.1 ((mem_bdryFull_iff_ne ht).not.1 hz)
    change extendTop t' ψ.hom x ≤ extendTop t' ψ.hom y ↔ x ≤ y
    by_cases hx : x ∈ P.bdryFull ⊤ <;> by_cases hy : y ∈ P.bdryFull ⊤
    · rw [extendTop_of_mem _ hx, extendTop_of_mem _ hy, Subtype.coe_le_coe]
      exact (orderIsoOfIso ψ).le_iff_le
    · rw [extendTop_of_mem _ hx, extendTop_of_notMem _ hy, heq hy]
      exact iff_of_true (ht' _) (ht x)
    · rw [extendTop_of_notMem _ hx, extendTop_of_mem _ hy, heq hx]
      exact iff_of_false (htop (ψ.hom ⟨y, hy⟩).2) (htop' hy)
    · rw [extendTop_of_notMem _ hx, extendTop_of_notMem _ hy, heq hx, heq hy]
      exact iff_of_true le_rfl le_rfl

theorem extendTopOrderIso_apply_of_mem {x : P} (h : x ∈ P.bdryFull ⊤) :
    extendTopOrderIso ht ht' ψ x = ψ.hom ⟨x, h⟩ :=
  extendTop_of_mem _ h

theorem extendTopOrderIso_apply_top : extendTopOrderIso ht ht' ψ t = t' :=
  extendTop_of_notMem _ fun h => (mem_bdryFull_iff_ne ht).1 h rfl

def isoOfBdryIso (hψ : ψ.IsSigned) : P ≅ Q :=
  isoMk (extendTopOrderIso ht ht' ψ) fun {x y} h => by
    by_cases hx : x ∈ P.bdryFull ⊤
    · have hy : y ∈ P.bdryFull ⊤ := (P.bdryFull ⊤).lower h.le hx
      have h' : (⟨y, hy⟩ : P.restrict (P.bdryFull ⊤)) ⋖ ⟨x, hx⟩ := (LowerSet.coe_covBy_coe _).1 h
      exact (Q.orient_congr (extendTopOrderIso_apply_of_mem ht ht' ψ hx)
        (extendTopOrderIso_apply_of_mem ht ht' ψ hy) _
        ((isMorphism (ψ.hom ≫ incl _)).covBy_apply h')).trans
        ((isMorphism (ψ.hom ≫ incl _)).orient_apply h')
    · obtain rfl : x = t := not_not.1 ((mem_bdryFull_iff_ne ht).not.1 hx)
      have hy : y ∈ P.bdryFull ⊤ := (mem_bdryFull_iff_ne ht).2 h.lt.ne
      have het : IsTop (extendTopOrderIso ht ht' ψ x) := by
        rw [extendTopOrderIso_apply_top]
        exact ht'
      refine ((orient_eq_iff_mem_bdry het _ _).2 ?_)
      rw [extendTopOrderIso_apply_of_mem ht ht' ψ hy]
      exact (hψ _ ⟨y, hy⟩).1 ((orient_eq_iff_mem_bdry ht h _).1 rfl)

end Extend

theorem IsAtom.isRound_restrict_bdry (hP : P.IsAtom) {n : ℕ}
    (hn : krullDim (⊤ : LowerSet P) = n + 1) (α : Bool) : (P.restrict (P.bdry ⊤ α)).IsRound ⊤ := by
  rw [← isRound_map_iff (incl _) ⊤, map_incl_top, bdry_eq_boundary hn]
  exact hP.isRound.boundary n α

theorem IsAtom.krullDim_restrict_bdry (hP : P.IsAtom) {n : ℕ}
    (hn : krullDim (⊤ : LowerSet P) = n + 1) (α : Bool) :
    krullDim (P.restrict (P.bdry ⊤ α)) = n := by
  rw [bdry_eq_boundary hn]
  exact hP.isMoleculeIn.krullDim_boundary (by rw [hn]; exact_mod_cast Nat.le_succ n) α

theorem nonempty_iso_rewrite (hP : P.IsAtom) {n : ℕ} (hn : krullDim (⊤ : LowerSet P) = n + 1) :
    Nonempty (P ≅ rewrite n (mergerGluing hP.isMoleculeIn (Iso.refl _) (Iso.refl _))
      (hP.isRound_restrict_bdry hn false) (hP.isRound_restrict_bdry hn true)
      (hP.krullDim_restrict_bdry hn false) (hP.krullDim_restrict_bdry hn true)) := by
  classical
  set φ := mergerGluing hP.isMoleculeIn (Iso.refl (P.restrict (P.bdry ⊤ false)))
    (Iso.refl (P.restrict (P.bdry ⊤ true)))
  have hU := hP.isRound_restrict_bdry hn false
  have hV := hP.isRound_restrict_bdry hn true
  have hUd := hP.krullDim_restrict_bdry hn false
  have hVd := hP.krullDim_restrict_bdry hn true
  obtain ⟨t, hT⟩ := hP.exists_eq_Iic
  have ht : IsTop t := fun x => (hT ▸ LowerSet.mem_top : x ∈ LowerSet.Iic t)
  have hpos : 0 < krullDim (⊤ : LowerSet P) := by
    rw [hn]
    exact_mod_cast Nat.succ_pos n
  obtain ⟨fA, hfA⟩ := exists_iso_restrict (rewrite.inl n φ hU hV hUd hVd)
    (rewrite.bdry_top_false n φ hU hV hUd hVd).symm
  obtain ⟨fB, hfB⟩ := exists_iso_restrict (rewrite.inr n φ hU hV hUd hVd)
    (rewrite.bdry_top_true n φ hU hV hUd hVd).symm
  have hA (x : P.restrict (P.bdry ⊤ false)) :
      (fA.hom x : rewrite n φ hU hV hUd hVd) = rewrite.inl n φ hU hV hUd hVd x :=
    ConcreteCategory.congr_hom hfA x
  have hB (y : P.restrict (P.bdry ⊤ true)) :
      (fB.hom y : rewrite n φ hU hV hUd hVd) = rewrite.inr n φ hU hV hUd hVd y :=
    ConcreteCategory.congr_hom hfB y
  have hc (x : P.restrict (P.bdry ⊤ false)) (y : P.restrict (P.bdry ⊤ true)) :
      ((Iso.refl (P.restrict (P.bdry ⊤ false))).hom x : P) =
          (Iso.refl (P.restrict (P.bdry ⊤ true))).hom y ↔
        (fA.hom x : rewrite n φ hU hV hUd hVd) = fB.hom y := by
    rw [hA, hB, rewrite.inl_eq_inr_iff, apply_eq_apply_iff_mergerGluing hP.isMoleculeIn
      (Iso.refl _) (Iso.refl _) hP.isRound hpos]
    exact ⟨fun ⟨h, hy⟩ => ⟨h, hy⟩, fun ⟨h, hy⟩ => ⟨h, hy⟩⟩
  exact ⟨isoOfBdryIso ht isTop_top (bdryIsoOfCover (Iso.refl _) (Iso.refl _) fA fB hc)
    (isSigned_bdryIsoOfCover _ _ _ _ hc)⟩

end Atoms.Molecule.OGP

import Atoms.Molecule.MoleculeShape.Basic
import Atoms.Molecule.Gluing.BoundaryIso

open CategoryTheory Order Atoms.Molecule.OGP

namespace Atoms.Molecule.MoleculeShape

variable (P : MoleculeShape) {n : ℕ}

theorem map_boundaryIncl_eq_bdry (hd : P.dimension = n + 1) (α : Bool) :
    map (P.boundaryIncl n α) ⊤ = P.ogp.bdry ⊤ α := by
  rw [map_boundaryIncl_top, bdry_eq_boundary (P.krullDim_top_eq hd)]

def bdryIso (hd : P.dimension = n + 1) (α : Bool) :
    (P.boundary n α).ogp ≅ P.ogp.restrict (P.ogp.bdry ⊤ α) :=
  (P.subIso _).symm ≪≫ restrictCongr (bdry_eq_boundary (P.krullDim_top_eq hd) α).symm

@[simp] theorem bdryIso_hom_apply (hd : P.dimension = n + 1) (α : Bool)
    (x : (P.boundary n α).ogp) : ((P.bdryIso hd α).hom x : P.ogp) = P.boundaryIncl n α x :=
  rfl

section Parallel

variable (V W : MoleculeShape) (φ : ∀ α, (V.boundary n α).ogp ≅ (W.boundary n α).ogp)
  (hV : V.IsRound) (hW : W.IsRound) (hdV : V.dimension = n + 1) (hdW : W.dimension = n + 1)

def bdryIsoOfParallel :
    V.ogp.restrict (V.ogp.bdryFull ⊤) ≅ W.ogp.restrict (W.ogp.bdryFull ⊤) :=
  bdryIsoOfCover (V.bdryIso hdV false) (V.bdryIso hdV true) (φ false ≪≫ W.bdryIso hdW false)
    (φ true ≪≫ W.bdryIso hdW true)
    (apply_eq_apply_iff_of_isRound V.isMolecule W.isMolecule hV hW
      (by rw [V.krullDim_top_eq hdV]; exact_mod_cast Nat.succ_pos n)
      (by rw [W.krullDim_top_eq hdW]; exact_mod_cast Nat.succ_pos n) _ _ _ _)

theorem isSigned_bdryIsoOfParallel : (bdryIsoOfParallel V W φ hV hW hdV hdW).IsSigned :=
  isSigned_bdryIsoOfCover _ _ _ _ _

@[reassoc (attr := simp)]
theorem toBdryFull_bdryIsoOfParallel_hom (α : Bool) :
    toBdryFull ((V.bdryIso hdV α).hom ≫ incl _) (map_hom_incl_top _) ≫
        (bdryIsoOfParallel V W φ hV hW hdV hdW).hom =
      toBdryFull ((φ α ≪≫ W.bdryIso hdW α).hom ≫ incl _) (map_hom_incl_top _) := by
  cases α
  · exact toBdryFull_bdryIsoOfCover_hom_left _ _ _ _ _
  · exact toBdryFull_bdryIsoOfCover_hom_right _ _ _ _ _

end Parallel

theorem bdryFull_eq_bot (hd : P.dimension = 0) : P.ogp.bdryFull ⊤ = ⊥ :=
  OGP.bdryFull_eq_bot (by rw [LowerSet.krullDim_top, krullDim_eq_dimension, hd, Nat.cast_zero])

theorem isEmpty_bdryFull (hd : P.dimension = 0) :
    IsEmpty (P.ogp.restrict (P.ogp.bdryFull ⊤)) :=
  ⟨fun x => (P.bdryFull_eq_bot hd ▸ x.2 : x.1 ∈ (⊥ : LowerSet P.ogp))⟩

def bdryIsoOfPoints (V W : MoleculeShape) (hV : V.dimension = 0)
    (hW : W.dimension = 0) :
    V.ogp.restrict (V.ogp.bdryFull ⊤) ≅ W.ogp.restrict (W.ogp.bdryFull ⊤) :=
  haveI := V.isEmpty_bdryFull hV
  haveI := W.isEmpty_bdryFull hW
  isoMk { toEquiv := Equiv.equivOfIsEmpty _ _, map_rel_iff' := fun {a} => isEmptyElim a }
    fun {x} => isEmptyElim x

theorem isSigned_bdryIsoOfPoints (V W : MoleculeShape) (hV : V.dimension = 0)
    (hW : W.dimension = 0) : (bdryIsoOfPoints V W hV hW).IsSigned :=
  haveI := V.isEmpty_bdryFull hV
  fun _ x => isEmptyElim x

private theorem krullDim_eq_dimension_of_eq {V W : MoleculeShape}
    (hd : V.dimension = W.dimension) : krullDim W.ogp = V.dimension := by
  rw [krullDim_eq_dimension, hd]

section RewriteAtom

variable (V W : MoleculeShape)
  (ψ : V.ogp.restrict (V.ogp.bdryFull ⊤) ≅ W.ogp.restrict (W.ogp.bdryFull ⊤))
  (hψ : ψ.IsSigned) (hV : V.IsRound) (hW : W.IsRound) (hd : V.dimension = W.dimension)
include hψ hV hW hd

def rewriteAtom : MoleculeShape :=
  ofOGP (rewrite V.dimension ψ (V.isRound_iff.1 hV) (W.isRound_iff.1 hW) V.krullDim_eq_dimension
      (krullDim_eq_dimension_of_eq hd))
    (rewrite.isMolecule _ _ _ _ _ _ hψ V.isMolecule W.isMolecule)

theorem isAtom_rewriteAtom : (rewriteAtom V W ψ hψ hV hW hd).ogp.IsAtom :=
  (isAtom_iff_of_iso (FiniteOGP.ofOGPIso _)).1
    (rewrite.isAtom _ _ _ _ _ _ hψ V.isMolecule W.isMolecule)

theorem isRound_rewriteAtom : (rewriteAtom V W ψ hψ hV hW hd).IsRound :=
  isRound_ofOGP _ _ (rewrite.isRound_top _ _ _ _ _ _ hψ)

theorem dimension_rewriteAtom :
    (rewriteAtom V W ψ hψ hV hW hd).dimension = V.dimension + 1 := by
  have h := dimension_ofOGP
    (rewrite V.dimension ψ (V.isRound_iff.1 hV) (W.isRound_iff.1 hW) V.krullDim_eq_dimension
      (krullDim_eq_dimension_of_eq hd))
    (rewrite.isMolecule _ _ _ _ _ _ hψ V.isMolecule W.isMolecule)
  rw [rewrite.krullDim_eq] at h
  exact_mod_cast h

def rewriteAtomIncl : (α : Bool) → (cond α W V).ogp ⟶ (rewriteAtom V W ψ hψ hV hW hd).ogp
  | false => rewrite.inl _ ψ _ _ _ _ ≫ (FiniteOGP.ofOGPIso _).hom
  | true => rewrite.inr _ ψ _ _ _ _ ≫ (FiniteOGP.ofOGPIso _).hom

instance (α : Bool) : IsInclusion (rewriteAtomIncl V W ψ hψ hV hW hd α) := by
  cases α
  · exact inferInstanceAs (IsInclusion (rewrite.inl _ ψ _ _ _ _ ≫ (FiniteOGP.ofOGPIso _).hom))
  · exact inferInstanceAs (IsInclusion (rewrite.inr _ ψ _ _ _ _ ≫ (FiniteOGP.ofOGPIso _).hom))

theorem map_rewriteAtomIncl (α : Bool) :
    map (rewriteAtomIncl V W ψ hψ hV hW hd α) ⊤ = (rewriteAtom V W ψ hψ hV hW hd).ogp.bdry ⊤ α := by
  cases α
  · change map (rewrite.inl _ ψ _ _ _ _ ≫ (FiniteOGP.ofOGPIso _).hom) ⊤ = _
    rw [map_comp, ← rewrite.bdry_top_false, map_bdry, map_top_of_isIso]
    rfl
  · change map (rewrite.inr _ ψ _ _ _ _ ≫ (FiniteOGP.ofOGPIso _).hom) ⊤ = _
    rw [map_comp, ← rewrite.bdry_top_true, map_bdry, map_top_of_isIso]
    rfl

theorem rewriteAtomIncl_false_eq_true_iff (x : V.ogp) (y : W.ogp) :
    rewriteAtomIncl V W ψ hψ hV hW hd false x = rewriteAtomIncl V W ψ hψ hV hW hd true y ↔
      ∃ hx : x ∈ V.ogp.bdryFull ⊤, (ψ.hom ⟨x, hx⟩).1 = y := by
  change (FiniteOGP.ofOGPIso _).hom (rewrite.inl _ ψ _ _ _ _ x) =
    (FiniteOGP.ofOGPIso _).hom (rewrite.inr _ ψ _ _ _ _ y) ↔ _
  rw [(IsInclusion.injective (f := (FiniteOGP.ofOGPIso _).hom)).eq_iff, rewrite.inl_eq_inr_iff]
  exact Iff.rfl

theorem map_rewriteAtomIncl_inf :
    map (rewriteAtomIncl V W ψ hψ hV hW hd false) ⊤ ⊓
        map (rewriteAtomIncl V W ψ hψ hV hW hd true) ⊤ =
      map (rewriteAtomIncl V W ψ hψ hV hW hd false) (V.ogp.bdryFull ⊤) := by
  change map (rewrite.inl _ ψ _ _ _ _ ≫ (FiniteOGP.ofOGPIso _).hom) ⊤ ⊓
      map (rewrite.inr _ ψ _ _ _ _ ≫ (FiniteOGP.ofOGPIso _).hom) ⊤ =
    map (rewrite.inl _ ψ _ _ _ _ ≫ (FiniteOGP.ofOGPIso _).hom) _
  rw [map_comp, map_comp, map_comp, ← map_inf, rewrite.map_inl_inf_map_inr]

end RewriteAtom

def boundaryIsoRewriteAtom (V W : MoleculeShape)
    (ψ : V.ogp.restrict (V.ogp.bdryFull ⊤) ≅ W.ogp.restrict (W.ogp.bdryFull ⊤)) (hψ : ψ.IsSigned)
    (hV : V.IsRound) (hW : W.IsRound) (hd : V.dimension = W.dimension) (α : Bool) :
    ((rewriteAtom V W ψ hψ hV hW hd).boundary V.dimension α).ogp ≅ (cond α W V).ogp :=
  ((rewriteAtom V W ψ hψ hV hW hd).subIso _).symm ≪≫
    (isoRestrictOfFintype (rewriteAtomIncl V W ψ hψ hV hW hd α) (by
      rw [map_rewriteAtomIncl, bdry_eq_boundary
        ((rewriteAtom V W ψ hψ hV hW hd).krullDim_top_eq (dimension_rewriteAtom ..))])).symm

end Atoms.Molecule.MoleculeShape

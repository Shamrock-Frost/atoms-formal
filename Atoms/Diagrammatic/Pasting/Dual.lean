import Atoms.Diagrammatic.Dual
import Atoms.Diagrammatic.Pasting.Boundary
import Atoms.Diagrammatic.Pasting.Units

open CategoryTheory Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic.PastingDiagram

variable {X Y : DiagSet.{u}} (J : ℕ → Bool)

@[implicit_reducible, simps]
def dual (u : PastingDiagram X) : PastingDiagram ((DiagSet.dual J).obj X) :=
  ⟨u.shape.dual J, realize.map (RDCpx.isoOfIso (P := (u.shape.dual J).rdc)
      (Q := (RDCpx.dualFunctor J).obj u.shape.rdc) (u.shape.dualIso J).symm).hom ≫
    (realizeDualIso J u.shape.rdc).hom ≫ (DiagSet.dual J).map u.map⟩

theorem dim_dual (u : PastingDiagram X) : (u.dual J).dim = u.dim :=
  u.shape.dimension_dual J

theorem isRound_dual_iff (u : PastingDiagram X) : (u.dual J).IsRound ↔ u.IsRound :=
  (isRound_top_iff_of_iso (u.shape.dualIso J)).trans (OGP.isRound_dual J)

theorem dual_mapTo (u : PastingDiagram X) (f : X ⟶ Y) :
    (u.mapTo f).dual J = (u.dual J).mapTo ((DiagSet.dual J).map f) := by
  simp only [dual, mapTo, Functor.map_comp, Category.assoc]

def Within.dual {a m : PastingDiagram X} (w : Within a m) : Within (a.dual J) (m.dual J) where
  emb := (a.shape.dualIso J).inv ≫ OGP.dualHom J w.emb ≫ (m.shape.dualIso J).hom
  comm := by
    have e : RDCpx.ofInclusion (P := (a.shape.dual J).rdc) (Q := (m.shape.dual J).rdc)
          ((a.shape.dualIso J).inv ≫ OGP.dualHom J w.emb ≫ (m.shape.dualIso J).hom) ≫
        (RDCpx.isoOfIso (P := (m.shape.dual J).rdc) (Q := (RDCpx.dualFunctor J).obj m.shape.rdc)
          (m.shape.dualIso J).symm).hom =
        (RDCpx.isoOfIso (P := (a.shape.dual J).rdc) (Q := (RDCpx.dualFunctor J).obj a.shape.rdc)
          (a.shape.dualIso J).symm).hom ≫
          (RDCpx.dualFunctor J).map
            (RDCpx.ofInclusion (P := a.shape.rdc) (Q := m.shape.rdc) w.emb) :=
      WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun x =>
        (m.shape.dualIso J).hom_inv_id_apply _)
    change realize.map _ ≫ realize.map _ ≫ (realizeDualIso J m.shape.rdc).hom ≫
      (DiagSet.dual J).map m.map = realize.map _ ≫ (realizeDualIso J a.shape.rdc).hom ≫
        (DiagSet.dual J).map a.map
    rw [← Category.assoc, ← realize.map_comp, e, realize.map_comp, Category.assoc,
      realizeDualIso_hom_naturality_assoc, ← Functor.map_comp, w.comm]

theorem Within.map_emb_dual {a m : PastingDiagram X} (w : Within a m) (S : LowerSet a.shape.ogp) :
    OGP.map (w.dual J).emb (OGP.map (a.shape.dualIso J).hom S) =
      OGP.map (m.shape.dualIso J).hom (OGP.map w.emb S : LowerSet m.shape.ogp) := by
  refine SetLike.coe_injective ?_
  simp only [coe_map, Within.dual, ConcreteCategory.coe_comp, Set.image_comp,
    Set.image_image, Iso.hom_inv_id_apply, Set.image_id']
  rfl

theorem Within.image_dual {a m : PastingDiagram X} (w : Within a m) :
    (w.dual J).image = OGP.map (m.shape.dualIso J).hom w.image :=
  (congrArg (OGP.map (w.dual J).emb) (map_top_of_isIso (a.shape.dualIso J).hom).symm).trans
    (w.map_emb_dual J ⊤)

theorem equiv_mapTo_dualDual (u : PastingDiagram X) :
    (((u.dual J).dual J).mapTo (DiagSet.dualDualIso J X).hom).Equiv u := by
  refine ⟨u.shape.dualDualIso J, ?_⟩
  ext T ⟨c⟩
  refine (congrArg (u.map.app T) (ULift.ext _ _ (WideSubcategory.hom_ext _
    (ConcreteCategory.hom_ext _ _ fun x => ?_)))).trans
      (NatTrans.naturality_apply u.map (Atom.dualDualIso J T.unop).inv.op _)
  exact congrArg (fun y => (u.shape.dualIso J).inv (((u.shape.dual J).dualIso J).inv
    (ConcreteCategory.hom c.hom y))) ((congrArg (T.unop.toMoleculeShape.dualIso J).inv
      (((T.unop.dual J).toMoleculeShape.dualIso J).hom_inv_id_apply _)).trans
        ((T.unop.toMoleculeShape.dualIso J).hom_inv_id_apply x)).symm

theorem equiv_dual_mapTo_dual (b : PastingDiagram ((DiagSet.dual J).obj X)) :
    (((b.dual J).mapTo (DiagSet.dualDualIso J X).hom).dual J).Equiv b := by
  rw [dual_mapTo, DiagSet.dual_map_dualDualIso_hom]
  exact equiv_mapTo_dualDual J b

theorem equiv_boundary_dual (u : PastingDiagram X) (k : ℕ) (α : Bool) :
    ((u.dual J).boundary k α).Equiv ((u.boundary k (xor (J (k + 1)) α)).dual J) :=
  Within.equiv_of_image_eq (Within.boundary (u.dual J) k α) ((Within.boundary u k _).dual J) (by
    rw [Within.image_boundary, Within.image_dual, Within.image_boundary, ← boundary_dual,
      map_boundary, map_top_of_isIso]
    rfl)

theorem equiv_boundary_dual_xor (u : PastingDiagram X) (k : ℕ) (α : Bool) :
    ((u.dual J).boundary k (xor (J (k + 1)) α)).Equiv ((u.boundary k α).dual J) := by
  have e := u.equiv_boundary_dual J k (xor (J (k + 1)) α)
  rwa [Bool.xor_xor_cancel_left] at e

theorem Equiv.dual {u v : PastingDiagram X} (h : u.Equiv v) : (u.dual J).Equiv (v.dual J) :=
  Within.equiv_of_image_eq ((Within.ofEquiv h).dual J) (Within.refl _) (by
    rw [Within.image_dual, Within.image_ofEquiv, map_top_of_isIso, Within.image_refl])

theorem dual_equiv_dual_iff {u v : PastingDiagram X} : (u.dual J).Equiv (v.dual J) ↔ u.Equiv v :=
  ⟨fun h => (equiv_mapTo_dualDual J u).symm.trans (((h.dual J).mapTo _).trans
    (equiv_mapTo_dualDual J v)), Equiv.dual J⟩

theorem pastable_dual_iff {u v : PastingDiagram X} {k : ℕ} :
    (cond (J (k + 1)) (v.dual J) (u.dual J)).Pastable
      (cond (J (k + 1)) (u.dual J) (v.dual J)) k ↔ u.Pastable v k := by
  have hu := u.equiv_boundary_dual J k
  have hv := v.equiv_boundary_dual J k
  have hd : min (u.dual J).dim (v.dual J).dim = min u.dim v.dim := by rw [dim_dual, dim_dual]
  cases hJ : J (k + 1)
  · simp only [hJ, Bool.false_xor] at hu hv
    refine and_congr ?_ (by rw [cond_false, cond_false, hd])
    exact Iff.trans ⟨fun h => (hu true).symm.trans (h.trans (hv false)),
      fun h => (hu true).trans (h.trans (hv false).symm)⟩ (dual_equiv_dual_iff J)
  · simp only [hJ, Bool.true_xor] at hu hv
    refine and_congr ?_ (by rw [cond_true, cond_true, min_comm, hd])
    exact Iff.trans ⟨fun h => (hv true).symm.trans (h.trans (hu false)),
      fun h => (hv true).trans (h.trans (hu false).symm)⟩
        ((dual_equiv_dual_iff J).trans ⟨Equiv.symm, Equiv.symm⟩)

theorem Pastable.dual {u v : PastingDiagram X} {k : ℕ} (h : u.Pastable v k) :
    (cond (J (k + 1)) (v.dual J) (u.dual J)).Pastable
      (cond (J (k + 1)) (u.dual J) (v.dual J)) k :=
  (pastable_dual_iff J).2 h

theorem equiv_dual_paste {u v : PastingDiagram X} {k : ℕ} (h : u.Pastable v k) :
    ((u.paste v k h).dual J).Equiv
      ((cond (J (k + 1)) (v.dual J) (u.dual J)).paste (cond (J (k + 1)) (u.dual J) (v.dual J)) k
        (h.dual J)) := by
  have hp := Within.isPastingIn_paste u v k h
  have hp' : ((u.paste v k h).dual J).shape.ogp.IsPastingIn k
      (Within.cond (J (k + 1)) ((Within.pasteInr u v k h).dual J)
        ((Within.pasteInl u v k h).dual J)).image
      (Within.cond (J (k + 1)) ((Within.pasteInl u v k h).dual J)
        ((Within.pasteInr u v k h).dual J)).image ⊤ := by
    rw [Within.image_cond, Within.image_cond, Within.image_dual, Within.image_dual,
      ← map_top_of_isIso ((u.paste v k h).shape.dualIso J).hom, ← Bool.apply_cond (OGP.map _),
      ← Bool.apply_cond (OGP.map _), isPastingIn_map_iff, isPastingIn_dual]
    cases J (k + 1) <;> exact hp
  exact ((equiv_paste_of_within _ _ hp' ((u.paste v k h).dual J).shape.isMolecule
    (h.dual J)).trans
    (Within.equiv_restrictTo_of_eq (Within.refl _) (Within.image_refl _) _).symm).symm

theorem equiv_dual_pasteAtBoundary (P Q : PastingDiagram X) (k : ℕ) (α : Bool)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤) (h : (P.boundary k (!α)).Equiv V)
    (ι' : Within (V.dual J) ((Q.dual J).boundary k (xor (J (k + 1)) α)))
    (hι' : ((Q.dual J).boundary k (xor (J (k + 1)) α)).shape.ogp.IsSubmoleculeOf ι'.image ⊤)
    (h' : ((P.dual J).boundary k (!xor (J (k + 1)) α)).Equiv (V.dual J))
    (himg : (ι'.trans (Within.boundary (Q.dual J) k (xor (J (k + 1)) α))).image =
      OGP.map (Q.shape.dualIso J).hom (ι.trans (Within.boundary Q k α)).image) :
    ((pasteAtBoundary P Q k α ι hι h).dual J).Equiv
      (pasteAtBoundary (P.dual J) (Q.dual J) k (xor (J (k + 1)) α) ι' hι' h') := by
  set m := pasteAtBoundary P Q k α ι hι h
  have hc : (m.dual J).shape.ogp.IsPastingAtIn k (xor (J (k + 1)) α)
      ((Within.pasteAtInl P Q k α ι hι h).dual J).image
      ((Within.pasteAtInr P Q k α ι hι h).dual J).image ⊤ := by
    rw [Within.image_dual, Within.image_dual, ← map_top_of_isIso (m.shape.dualIso J).hom]
    refine IsPastingAtIn.map (m.shape.dualIso J).hom ((isPastingAtIn_dual J).2 ?_)
    rw [Bool.xor_xor_cancel_left]
    exact Within.isPastingAtIn_pasteAt P Q k α ι hι h
  have hmeet : (ι'.trans ((Within.boundary (Q.dual J) k (xor (J (k + 1)) α)).trans
      ((Within.pasteAtInr P Q k α ι hι h).dual J))).image =
      ((Within.pasteAtInl P Q k α ι hι h).dual J).image ⊓
        ((Within.pasteAtInr P Q k α ι hι h).dual J).image := by
    rw [Within.image_trans_assoc, himg, Within.map_emb_dual, ← Within.image_trans_assoc,
      image_occurrence_pasteAt, map_inf, Within.image_dual, Within.image_dual]
  exact ((equiv_pasteAtBoundary_of_within _ _ hc ι' hι' hmeet h').trans
    (Within.equiv_restrictTo_of_eq (Within.refl _) (Within.image_refl _) _).symm).symm

theorem equiv_dual_unit (u : PastingDiagram X) : (u.unit.dual ⊤).Equiv (u.dual ⊤).unit := by
  refine ⟨unitShapeDualIso u.shape, ?_⟩
  have e := isoOfIso_unitShapeDualIso_comp_cylProj u.shape
  change realize.map _ ≫ realize.map (cylProj (u.shape.dual ⊤) ((u.shape.dual ⊤).ogp.bdryFull ⊤)) ≫
      realize.map (RDCpx.isoOfIso (P := (u.shape.dual ⊤).rdc)
        (Q := (RDCpx.dualFunctor ⊤).obj u.shape.rdc) (u.shape.dualIso ⊤).symm).hom ≫
        (realizeDualIso ⊤ u.shape.rdc).hom ≫ (DiagSet.dual ⊤).map u.map =
    realize.map (RDCpx.isoOfIso (P := ((unitShape u.shape).dual ⊤).rdc)
        (Q := (RDCpx.dualFunctor ⊤).obj (unitShape u.shape).rdc)
        ((unitShape u.shape).dualIso ⊤).symm).hom ≫ (realizeDualIso ⊤ (unitShape u.shape).rdc).hom ≫
      (DiagSet.dual ⊤).map (realize.map (cylProj u.shape (u.shape.ogp.bdryFull ⊤)) ≫ u.map)
  rw [← realize.map_comp_assoc, ← realize.map_comp_assoc, Category.assoc, e,
    realize.map_comp_assoc, realizeDualIso_hom_naturality_assoc, Functor.map_comp]

end Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

open PastingDiagram

variable {X : DiagSet.{u}}

variable (J : ℕ → Bool)

def RoundPastingDiagram.dual (u : RoundPastingDiagram X) :
    RoundPastingDiagram ((DiagSet.dual J).obj X) :=
  ⟨u.toPastingDiagram.dual J, (isRound_dual_iff J _).2 u.isRound⟩

@[simp] theorem RoundPastingDiagram.toPastingDiagram_dual (u : RoundPastingDiagram X) :
    (u.dual J).toPastingDiagram = u.toPastingDiagram.dual J :=
  rfl

theorem Parallel.dual {u v : RoundPastingDiagram X} (h : Parallel u v) :
    Parallel (u.dual J) (v.dual J) := by
  have hu : (u.dual J).dim = u.dim := dim_dual J u.toPastingDiagram
  have hv : (v.dual J).dim = v.dim := dim_dual J v.toPastingDiagram
  refine ⟨hu.trans (h.1.trans hv.symm), h.2.imp (hu.trans ·) fun hb α => ?_⟩
  change ((u.toPastingDiagram.dual J).boundary ((u.dual J).dim - 1) α).Equiv
    ((v.toPastingDiagram.dual J).boundary ((v.dual J).dim - 1) α)
  rw [hu, hv, ← h.1]
  have hb' (β : Bool) : (u.boundary (u.dim - 1) β).Equiv (v.boundary (u.dim - 1) β) := by
    have e := hb β
    rwa [← h.1] at e
  exact (equiv_boundary_dual J u.toPastingDiagram (u.dim - 1) α).trans
    (((hb' _).dual J).trans (equiv_boundary_dual J v.toPastingDiagram (u.dim - 1) α).symm)

end Atoms.Diagrammatic

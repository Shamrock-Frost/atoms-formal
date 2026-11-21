import Atoms.Diagrammatic.Pasting.Units
import Atoms.Molecule.Cylinder.Inverted

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

theorem principalInclusionRDC_comp_mem_closure {U Q : RDCpx.{0}} [FinEnum U.obj.toOGP]
    [DecidableLE U.obj.toOGP] (p : U ⟶ Q) (x : U.obj.toOGP) (b : (principalAtomRDC U x).ogp) :
    ConcreteCategory.hom (principalInclusionRDC U x ≫ p).hom b ∈
      LowerSet.Iic (ConcreteCategory.hom p.hom x) :=
  (ConcreteCategory.hom p.hom).isMap.monotone (principalInclusionRDC_mem_closure U x b)

theorem isCollapseHom_principalLiftRDC {U Q : RDCpx.{0}} [FinEnum U.obj.toOGP]
    [DecidableLE U.obj.toOGP] [FinEnum Q.obj.toOGP] [DecidableLE Q.obj.toOGP] (p : U ⟶ Q)
    (x : U.obj.toOGP) :
    IsCollapseHom (principalLiftRDC Q (ConcreteCategory.hom p.hom x) (principalInclusionRDC U x ≫ p)
      (principalInclusionRDC_comp_mem_closure p x)) := by
  intro a
  obtain ⟨y, hyx, hya⟩ := (ConcreteCategory.hom p.hom).isMap.fibration
    (principalInclusionRDC_mem_closure Q (ConcreteCategory.hom p.hom x) a)
  obtain ⟨b, rfl⟩ : y ∈ Set.range (ConcreteCategory.hom (principalInclusionRDC U x).hom) := by
    rw [image_principalInclusionRDC]
    exact hyx
  refine ⟨b, injective_principalInclusionRDC Q _ ?_⟩
  exact (congrArg (fun f : atomToRDCpx.obj _ ⟶ Q => ConcreteCategory.hom f.hom b)
    (principalLiftRDC_comp_principalInclusionRDC Q _ _ _)).trans hya

theorem app_eq_map_principalLiftRDC {Q : RDCpx.{0}} [FinEnum Q.obj.toOGP]
    [DecidableLE Q.obj.toOGP] (w : realize.obj Q ⟶ X) (q : Q.obj.toOGP) {T : Atom}
    (c : atomToRDCpx.obj T ⟶ Q) (hc : ∀ t, ConcreteCategory.hom c.hom t ∈ LowerSet.Iic q) :
    w.app (op T) ⟨c⟩ =
      X.map (principalLiftRDC Q q c hc).op (w.app (op _) ⟨principalInclusionRDC Q q⟩) :=
  (congrArg (w.app (op T))
    (congrArg ULift.up (principalLiftRDC_comp_principalInclusionRDC Q q c hc))).symm.trans
    (NatTrans.naturality_apply w (principalLiftRDC Q q c hc).op ⟨principalInclusionRDC Q q⟩)

theorem realize_map_comp_eq_of_apply_eq {U R Q Q' : RDCpx.{0}} [Finite U.obj.toOGP]
    [Finite Q.obj.toOGP] [Finite Q'.obj.toOGP] (p : U ⟶ Q) (p' : U ⟶ Q')
    (w : realize.obj Q ⟶ X) (w' : realize.obj Q' ⟶ X)
    (h : realize.map p ≫ w = realize.map p' ≫ w') (g : R.obj.toOGP → U.obj.toOGP)
    (hg : ∀ x y, x ≤ y → g x ≤ g y) (d : R ⟶ Q) (d' : R ⟶ Q')
    (hd : ∀ y, ConcreteCategory.hom d.hom y = ConcreteCategory.hom p.hom (g y))
    (hd' : ∀ y, ConcreteCategory.hom d'.hom y = ConcreteCategory.hom p'.hom (g y)) :
    realize.map d ≫ w = realize.map d' ≫ w' := by
  classical
  have (P : RDCpx.{0}) [Finite P.obj.toOGP] : FinEnum P.obj.toOGP :=
    have := Fintype.ofFinite P.obj.toOGP
    FinEnum.ofList Finset.univ.toList fun x => Finset.mem_toList.2 (Finset.mem_univ x)
  ext ⟨T⟩ ⟨c : atomToRDCpx.obj T ⟶ R⟩
  change w.app (op T) ⟨c ≫ d⟩ = w'.app (op T) ⟨c ≫ d'⟩
  let x := g (ConcreteCategory.hom c.hom T.top)
  have hle (t : T.ogp) : g (ConcreteCategory.hom c.hom t) ≤ x :=
    hg _ _ ((ConcreteCategory.hom c.hom).isMap.monotone (T.le_top t))
  have hc (t : T.ogp) : ConcreteCategory.hom (c ≫ d).hom t ∈
      LowerSet.Iic (ConcreteCategory.hom p.hom x) :=
    LowerSet.mem_Iic_iff.2 ((hd _).trans_le ((ConcreteCategory.hom p.hom).isMap.monotone (hle t)))
  have hc' (t : T.ogp) : ConcreteCategory.hom (c ≫ d').hom t ∈
      LowerSet.Iic (ConcreteCategory.hom p'.hom x) :=
    LowerSet.mem_Iic_iff.2
      ((hd' _).trans_le ((ConcreteCategory.hom p'.hom).isMap.monotone (hle t)))
  let A := principalAtomRDC Q (ConcreteCategory.hom p.hom x)
  let A' := principalAtomRDC Q' (ConcreteCategory.hom p'.hom x)
  let r₀ : principalAtomRDC U x ⟶ A := principalLiftRDC Q _
    (principalInclusionRDC U x ≫ p) (principalInclusionRDC_comp_mem_closure p x)
  let r₀' : principalAtomRDC U x ⟶ A' := principalLiftRDC Q' _
    (principalInclusionRDC U x ≫ p') (principalInclusionRDC_comp_mem_closure p' x)
  let r : T ⟶ A := principalLiftRDC Q _ (c ≫ d) hc
  let r' : T ⟶ A' := principalLiftRDC Q' _ (c ≫ d') hc'
  let a : X.obj (op A) := w.app (op A) ⟨principalInclusionRDC Q _⟩
  let a' : X.obj (op A') := w'.app (op A') ⟨principalInclusionRDC Q' _⟩
  have hu : X.map r₀.op a = X.map r₀'.op a' := by
    have h0 : w.app (op (principalAtomRDC U x)) ⟨principalInclusionRDC U x ≫ p⟩ =
        w'.app (op (principalAtomRDC U x)) ⟨principalInclusionRDC U x ≫ p'⟩ :=
      congrArg (fun m => m.app (op (principalAtomRDC U x)) ⟨principalInclusionRDC U x⟩) h
    exact (app_eq_map_principalLiftRDC w _ _ _).symm.trans
      (h0.trans (app_eq_map_principalLiftRDC w' _ _ _))
  obtain ⟨Z, s, z, hs, hz, hsz⟩ := Homotopical.EZCategory.exists_isNondegenerate X A a
  obtain ⟨Z', s', z', hs', hz', hsz'⟩ := Homotopical.EZCategory.exists_isNondegenerate X A' a'
  have hsp : IsSplitEpi (r₀ ≫ s) :=
    IsSplitEpi.mk' ((isSplitEpi_of_isCollapseHom r₀
      (isCollapseHom_principalLiftRDC p x)).exists_splitEpi.some.comp hs.exists_splitEpi.some)
  have hsp' : IsSplitEpi (r₀' ≫ s') :=
    IsSplitEpi.mk' ((isSplitEpi_of_isCollapseHom r₀'
      (isCollapseHom_principalLiftRDC p' x)).exists_splitEpi.some.comp hs'.exists_splitEpi.some)
  have heq : X.map (r₀ ≫ s).op z = X.map (r₀' ≫ s').op z' := by
    calc X.map (r₀ ≫ s).op z = X.map r₀.op (X.map s.op z) :=
          Functor.map_comp_apply X s.op r₀.op z
      _ = X.map r₀.op a := congrArg (X.map r₀.op) hsz
      _ = X.map r₀'.op a' := hu
      _ = X.map r₀'.op (X.map s'.op z') := congrArg (X.map r₀'.op) hsz'.symm
      _ = X.map (r₀' ≫ s').op z' := (Functor.map_comp_apply X s'.op r₀'.op z').symm
  obtain ⟨e, ⟨he, hez⟩, -⟩ := Homotopical.EZCategory.existsUnique_iso_of_isNondegenerate X
    (r₀ ≫ s) (r₀' ≫ s') z z' hsp hz hsp' hz' heq
  have key : r ≫ s ≫ e.hom = r' ≫ s' := by
    refine Atom.hom_ext fun t => ?_
    obtain ⟨b, hb⟩ : g (ConcreteCategory.hom c.hom t) ∈
        Set.range (ConcreteCategory.hom (principalInclusionRDC U x).hom) := by
      rw [image_principalInclusionRDC]
      exact hle t
    have e₁ : r t = r₀ b := injective_principalInclusionRDC Q _ (by
      have h1 := congrArg (fun f : atomToRDCpx.obj T ⟶ Q => ConcreteCategory.hom f.hom t)
        (principalLiftRDC_comp_principalInclusionRDC Q _ (c ≫ d) hc)
      have h2 := congrArg (fun f : atomToRDCpx.obj (principalAtomRDC U x) ⟶ Q =>
        ConcreteCategory.hom f.hom b) (principalLiftRDC_comp_principalInclusionRDC Q _
          (principalInclusionRDC U x ≫ p) (principalInclusionRDC_comp_mem_closure p x))
      refine h1.trans (Eq.trans ?_ h2.symm)
      change ConcreteCategory.hom d.hom (ConcreteCategory.hom c.hom t) =
        ConcreteCategory.hom p.hom (ConcreteCategory.hom (principalInclusionRDC U x).hom b)
      rw [hd, hb])
    have e₂ : r' t = r₀' b := injective_principalInclusionRDC Q' _ (by
      have h1 := congrArg (fun f : atomToRDCpx.obj T ⟶ Q' => ConcreteCategory.hom f.hom t)
        (principalLiftRDC_comp_principalInclusionRDC Q' _ (c ≫ d') hc')
      have h2 := congrArg (fun f : atomToRDCpx.obj (principalAtomRDC U x) ⟶ Q' =>
        ConcreteCategory.hom f.hom b) (principalLiftRDC_comp_principalInclusionRDC Q' _
          (principalInclusionRDC U x ≫ p') (principalInclusionRDC_comp_mem_closure p' x))
      refine h1.trans (Eq.trans ?_ h2.symm)
      change ConcreteCategory.hom d'.hom (ConcreteCategory.hom c.hom t) =
        ConcreteCategory.hom p'.hom (ConcreteCategory.hom (principalInclusionRDC U x).hom b)
      rw [hd', hb])
    have e₃ := ConcreteCategory.congr_hom he b
    simp only [ConcreteCategory.comp_apply] at e₃ ⊢
    rw [e₁, e₂]
    exact e₃
  calc w.app (op T) ⟨c ≫ d⟩ = X.map r.op a := app_eq_map_principalLiftRDC w _ (c ≫ d) hc
    _ = X.map r.op (X.map s.op (X.map e.hom.op z')) := by rw [hez, hsz]
    _ = X.map (r ≫ s ≫ e.hom).op z' := by
        rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    _ = X.map (r' ≫ s').op z' := by rw [key]
    _ = X.map r'.op (X.map s'.op z') := Functor.map_comp_apply X s'.op r'.op z'
    _ = X.map r'.op a' := by rw [hsz']
    _ = w'.app (op T) ⟨c ≫ d'⟩ := (app_eq_map_principalLiftRDC w' _ (c ≫ d') hc').symm

end Atoms.Diagrammatic

namespace Atoms.Diagrammatic.PastingDiagram

variable {X Y : DiagSet.{u}}

theorem DegeneracyFactorization.grade_lt {u : PastingDiagram X} (f : DegeneracyFactorization u)
    (x : f.target.obj.toOGP) : grade ℕ x < u.dim := by
  exact_mod_cast (grade_le_krullDim x).trans_lt f.dim_lt

@[implicit_reducible, simps]
noncomputable def reverse (u : PastingDiagram X) (hu : u.IsDegenerate) : PastingDiagram X :=
  ⟨u.shape.dual (OGP.topDim u.shape.dimension),
    realize.map (MoleculeShape.dualLift hu.factorization.proj
      fun x => decide_eq_false (hu.factorization.grade_lt x).ne) ≫ hu.factorization.map⟩

private theorem equiv_dualLift_of_eq {u v : PastingDiagram X} (h : u.Equiv v)
    (hu : u.IsDegenerate) (hv : v.IsDegenerate) {J J' : ℕ → Bool} (hJ : J = J')
    (hJu : ∀ x : hu.factorization.target.obj.toOGP, J (grade ℕ x) = false)
    (hJv : ∀ x : hv.factorization.target.obj.toOGP, J' (grade ℕ x) = false) :
    PastingDiagram.Equiv
      ⟨u.shape.dual J,
        realize.map (MoleculeShape.dualLift hu.factorization.proj hJu) ≫ hu.factorization.map⟩
      ⟨v.shape.dual J',
        realize.map (MoleculeShape.dualLift hv.factorization.proj hJv) ≫ hv.factorization.map⟩ := by
  subst hJ
  obtain ⟨ψ, hψ⟩ := h
  have : Finite hv.factorization.target.obj.toOGP :=
    Finite.of_surjective _ hv.factorization.surjective
  have : Finite hu.factorization.target.obj.toOGP :=
    Finite.of_surjective _ hu.factorization.surjective
  refine ⟨(u.shape.dualIso J).symm ≪≫ (dualFunctor J).mapIso ψ ≪≫ v.shape.dualIso J,
    (realize.map_comp_assoc _ _ _).symm.trans ?_⟩
  refine realize_map_comp_eq_of_apply_eq (U := u.shape.rdc) (R := (u.shape.dual J).rdc)
    ((RDCpx.isoOfIso (P := u.shape.rdc) (Q := v.shape.rdc) ψ).hom ≫ hv.factorization.proj)
    hu.factorization.proj _ _ ?_ (fun y => (u.shape.dualIso J).inv y)
    (fun x y hxy => (isMorphism (u.shape.dualIso J).inv).monotone hxy) _ _ (fun y => ?_)
    (fun _ => rfl)
  · rw [realize.map_comp, Category.assoc, hv.factorization.comp_eq, hψ, hu.factorization.comp_eq]
  · exact congrArg (ConcreteCategory.hom hv.factorization.proj.hom)
      ((v.shape.dualIso J).hom_inv_id_apply (ψ.hom ((u.shape.dualIso J).inv y)))

theorem Equiv.reverse {u v : PastingDiagram X} (h : u.Equiv v) (hu : u.IsDegenerate)
    (hv : v.IsDegenerate) : (u.reverse hu).Equiv (v.reverse hv) :=
  equiv_dualLift_of_eq h hu hv (congrArg OGP.topDim (dim_eq_of_equiv h)) _ _

theorem dim_reverse (u : PastingDiagram X) (hu : u.IsDegenerate) : (u.reverse hu).dim = u.dim :=
  u.shape.dimension_dual _

theorem isDegenerate_reverse (u : PastingDiagram X) (hu : u.IsDegenerate) :
    (u.reverse hu).IsDegenerate :=
  ⟨hu.factorization.target, MoleculeShape.dualLift hu.factorization.proj
      (fun x => decide_eq_false (hu.factorization.grade_lt x).ne), hu.factorization.map,
    MoleculeShape.surjective_dualLift _ _ hu.factorization.surjective,
    hu.factorization.dim_lt.trans_eq (by rw [dim_reverse]), rfl⟩

theorem isRound_reverse {u : PastingDiagram X} (hu : u.IsDegenerate) (hr : u.IsRound) :
    (u.reverse hu).IsRound :=
  MoleculeShape.isRound_dual hr _

theorem dim_pos_of_isDegenerate {u : PastingDiagram X} (hu : u.IsDegenerate) : 0 < u.dim := by
  obtain ⟨x, -⟩ := u.shape.isMolecule.nonempty
  exact (Nat.zero_le _).trans_lt
    (hu.factorization.grade_lt (ConcreteCategory.hom hu.factorization.proj.hom x))

theorem boundary_reverse (u : PastingDiagram X) (hu : u.IsDegenerate) (α : Bool) :
    ((u.reverse hu).boundary (u.dim - 1) α).Equiv (u.boundary (u.dim - 1) (!α)) := by
  have hn : 0 < u.shape.dimension := dim_pos_of_isDegenerate hu
  have hJ : ∀ m ≤ u.dim - 1, OGP.topDim u.shape.dimension m = false := fun m hm =>
    decide_eq_false (by rw [dim_def] at hm; omega)
  refine equiv_of_emb_of_image_eq (a := (u.reverse hu).boundary (u.dim - 1) α)
    (b := u.boundary (u.dim - 1) (!α)) (C := u.shape.rdc) u.map
    (u.shape.boundaryDualIncl hJ α) (u.shape.boundaryIncl (u.dim - 1) (!α)) ?_ rfl ?_
  · rw [← hu.factorization.comp_eq, ← Category.assoc, ← realize.map_comp]
    change _ = realize.map
        ((u.shape.dual (OGP.topDim u.shape.dimension)).boundaryInclRDC
          (u.dim - 1) α) ≫
      realize.map (MoleculeShape.dualLift hu.factorization.proj
        fun x => decide_eq_false (hu.factorization.grade_lt x).ne) ≫ hu.factorization.map
    rw [← Category.assoc, ← realize.map_comp]
    rfl
  · rw [MoleculeShape.map_boundaryDualIncl_top, MoleculeShape.map_boundaryIncl_top, dim_def,
      Nat.sub_add_cancel hn, OGP.topDim, decide_eq_true rfl, Bool.true_xor]

theorem reverse_mapTo (u : PastingDiagram X) (hu : u.IsDegenerate) (f : X ⟶ Y)
    (hf : (u.mapTo f).IsDegenerate) :
    ((u.reverse hu).mapTo f).Equiv ((u.mapTo f).reverse hf) := by
  have : Finite hu.factorization.target.obj.toOGP :=
    Finite.of_surjective _ hu.factorization.surjective
  have : Finite hf.factorization.target.obj.toOGP :=
    Finite.of_surjective _ hf.factorization.surjective
  refine ⟨Iso.refl _, ?_⟩
  change realize.map (𝟙 _) ≫ ((u.mapTo f).reverse hf).map = ((u.reverse hu).mapTo f).map
  rw [realize.map_id, Category.id_comp, reverse_map, mapTo_map, reverse_map, Category.assoc]
  refine (realize_map_comp_eq_of_apply_eq (U := u.shape.rdc)
    (R := (u.shape.dual (Molecule.OGP.topDim u.shape.dimension)).rdc) hf.factorization.proj
    hu.factorization.proj hf.factorization.map (hu.factorization.map ≫ f) ?_
    (fun y => (u.shape.dualIso _).inv y)
    (fun x y hxy => (Molecule.OGP.isMorphism (u.shape.dualIso _).inv).monotone hxy) _ _
    (fun _ => rfl) (fun _ => rfl))
  rw [hf.factorization.comp_eq, ← Category.assoc, hu.factorization.comp_eq, mapTo_map]

end Atoms.Diagrammatic.PastingDiagram

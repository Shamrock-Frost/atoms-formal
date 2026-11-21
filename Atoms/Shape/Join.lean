import Atoms.Molecule.Construction.JoinInclusion
import Atoms.Shape.Dual
import Atoms.Shape.Rigidity
import Atoms.Shape.Standard

open CategoryTheory Order Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Shape

def atomJoin (U V : Atom) : Atom :=
  Atom.ofOGP (join U.ogp V.ogp) (isAtom_join _ _ U.isAtom V.isAtom)

def joinHom {U U' V V' : Atom} (f : U ⟶ U') (g : V ⟶ V') : atomJoin U V ⟶ atomJoin U' V' :=
  haveI := Atom.functor_isFibered f
  haveI := Atom.functor_isFibered g
  haveI := functor_isFibered_joinMap (Atom.isMap f).monotone (Atom.isMap g).monotone
  Atom.conjHom (FiniteOGP.ofOGPIso _) (FiniteOGP.ofOGPIso _) (joinMap f g)
    (isMap_joinMap U.isRDC U'.isRDC V.isRDC V'.isRDC (Atom.isMap f) (Atom.isMap g))

def joinFunctor : Atom × Atom ⥤ Atom where
  obj p := atomJoin p.1 p.2
  map f := joinHom f.1 f.2
  map_id _ := Atom.hom_ext fun x =>
    (congrArg _ (congrFun joinMap_id _)).trans (Iso.inv_hom_id_apply _ x)
  map_comp {_ _ r} f g := Atom.hom_ext fun _ =>
    (congrArg _ (congrFun (joinMap_comp f.1 g.1 f.2 g.2) _)).trans
      (congrArg (fun w => (FiniteOGP.ofOGPIso (join r.1.ogp r.2.ogp)).hom (joinMap g.1 g.2 w))
        (Iso.hom_inv_id_apply _ _).symm)

@[simp] theorem joinHom_id (U V : Atom) : joinHom (𝟙 U) (𝟙 V) = 𝟙 (atomJoin U V) :=
  joinFunctor.map_id (U, V)

@[reassoc] theorem joinHom_comp {U U' U'' V V' V'' : Atom} (f : U ⟶ U') (f' : U' ⟶ U'')
    (g : V ⟶ V') (g' : V' ⟶ V'') : joinHom (f ≫ f') (g ≫ g') = joinHom f g ≫ joinHom f' g' :=
  joinFunctor.map_comp (X := (U, V)) (Y := (U', V')) (Z := (U'', V'')) (f, g) (f', g')

theorem joinHom_apply {U U' V V' : Atom} (f : U ⟶ U') (g : V ⟶ V')
    (x : (atomJoin U V).ogp) :
    joinHom f g x = (FiniteOGP.ofOGPIso (join U'.ogp V'.ogp)).hom
      (joinMap f g ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv x)) :=
  rfl

def joinInclLeftHom (U V : Atom) : U ⟶ atomJoin U V :=
  haveI := (isLocalEmbedding_of_isInclusion (join.inl U.ogp V.ogp)).functor_isFibered
  Atom.conjHom (Iso.refl U.ogp) (FiniteOGP.ofOGPIso _) (join.inl U.ogp V.ogp)
    (isMap_of_isInclusion (join.inl U.ogp V.ogp))

def joinInclRightHom (U V : Atom) : V ⟶ atomJoin U V :=
  haveI := (isLocalEmbedding_of_isInclusion (join.inr U.ogp V.ogp)).functor_isFibered
  Atom.conjHom (Iso.refl V.ogp) (FiniteOGP.ofOGPIso _) (join.inr U.ogp V.ogp)
    (isMap_of_isInclusion (join.inr U.ogp V.ogp))

theorem isInclusionHom_joinInclLeftHom (U V : Atom) : IsInclusionHom (joinInclLeftHom U V) := by
  have := (isLocalEmbedding_of_isInclusion (join.inl U.ogp V.ogp)).functor_isFibered
  exact Atom.isInclusionHom_conjHom _ _ _ (injective_joinInclLeft U.ogp V.ogp)

@[reassoc] theorem joinInclLeftHom_comp_joinHom {U U' V V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    joinInclLeftHom U V ≫ joinHom f g = f ≫ joinInclLeftHom U' V' :=
  Atom.hom_ext fun x => (congrArg (fun w => (FiniteOGP.ofOGPIso (join U'.ogp V'.ogp)).hom
    (joinMap f g w)) (Iso.hom_inv_id_apply _ _)).trans (congrArg _ (joinMap_joinInclLeft f g x))

@[reassoc] theorem joinInclRightHom_comp_joinHom {U U' V V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    joinInclRightHom U V ≫ joinHom f g = g ≫ joinInclRightHom U' V' :=
  Atom.hom_ext fun x => (congrArg (fun w => (FiniteOGP.ofOGPIso (join U'.ogp V'.ogp)).hom
    (joinMap f g w)) (Iso.hom_inv_id_apply _ _)).trans (congrArg _ (joinMap_joinInclRight f g x))

theorem isInclusionHom_joinHom {U U' V V' : Atom} {f : U ⟶ U'} {g : V ⟶ V'}
    (hf : IsInclusionHom f) (hg : IsInclusionHom g) : IsInclusionHom (joinHom f g) := by
  have := Atom.functor_isFibered f
  have := Atom.functor_isFibered g
  have := functor_isFibered_joinMap (Atom.isMap f).monotone (Atom.isMap g).monotone
  exact Atom.isInclusionHom_conjHom _ _ _ (injective_joinMap hf hg)

theorem dimension_atomJoin (U V : Atom) :
    (atomJoin U V).dimension = U.dimension + V.dimension + 1 := by
  set t : join U.ogp V.ogp := ⟨((U.top : WithBot U.ogp), (V.top : WithBot V.ogp)),
    fun h => WithBot.coe_ne_bot (congrArg Prod.fst h)⟩
  have htop : (⊤ : LowerSet (join U.ogp V.ogp)) = LowerSet.Iic t :=
    le_antisymm (fun p _ => join_le_iff.2 ⟨WithBot.le_coe_iff.2 fun x _ => U.le_top x,
      WithBot.le_coe_iff.2 fun y _ => V.le_top y⟩) le_top
  have hk : krullDim (atomJoin U V).ogp = ((U.dimension + V.dimension + 1 : ℕ) : WithBot ℕ∞) := by
    refine (krullDim_eq_of_orderIso
      (orderIsoOfIso (FiniteOGP.ofOGPIso (join U.ogp V.ogp)))).symm.trans ?_
    rw [← LowerSet.krullDim_top, htop, LowerSet.krullDim_Iic, grade_join]
    change ((grade ℕ U.top + 1 + (grade ℕ V.top + 1) - 1 : ℕ) : WithBot ℕ∞) = _
    rw [← U.dimension_eq, ← V.dimension_eq]
    congr 2
    omega
  exact_mod_cast (atomJoin U V).krullDim_eq_dimension.symm.trans hk

theorem nonempty_iso_atomGlobe_of_dimension_eq_one {U : Atom} (hU : U.dimension = 1) :
    Nonempty (atomGlobe 1 ≅ U) := by
  have hb : ∀ V : Atom, ∀ α,
      krullDim (⊤ : LowerSet (V.toMoleculeShape.boundary 0 α).ogp) = 0 := fun V α => by
    rw [LowerSet.krullDim_top, MoleculeShape.krullDim_eq_dimension,
      MoleculeShape.dimension_boundary _ (Nat.zero_le _) α, Nat.cast_zero]
  obtain ⟨φ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso (atomGlobe 1).toMoleculeShape
    U.toMoleculeShape (n := 0)
    (fun α => (nonempty_iso_of_krullDim_eq_zero
      ((atomGlobe 1).toMoleculeShape.boundary 0 α).isMolecule
      (U.toMoleculeShape.boundary 0 α).isMolecule (hb _ α) (hb U α)).some)
    (atomGlobe 1).isAtom U.isAtom (dimension_atomGlobe 1) hU
  exact ⟨Atom.isoOfIso φ⟩

theorem exists_arrow_apply_top {U : Atom} {a : U.ogp} (ha : grade ℕ a = 1) :
    ∃ g : atomGlobe 1 ⟶ U, g (atomGlobe 1).top = a := by
  obtain ⟨i⟩ := nonempty_iso_atomGlobe_of_dimension_eq_one (U := Atom.ofClosure U a)
    (by rw [Atom.dimension_ofClosure, ha])
  exact ⟨i.hom ≫ Atom.closureIncl U a,
    (congrArg (Atom.closureIncl U a) (isCollapseHom_of_iso i).apply_top).trans
      (Atom.closureIncl_top U a)⟩

end Atoms.Shape

namespace Atoms.Shape.Atom

def joinDualIso (U V : Atom) :
    (atomJoin U V).dual Nat.bodd ≅ atomJoin (V.dual Nat.bodd) (U.dual Nat.bodd) :=
  isoOfIso (((atomJoin U V).toMoleculeShape.dualIso Nat.bodd).symm ≪≫
    (OGP.dualFunctor Nat.bodd).mapIso (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).symm ≪≫
    joinSwap U.ogp V.ogp ≪≫
    join.mapIso (V.toMoleculeShape.dualIso Nat.bodd) (U.toMoleculeShape.dualIso Nat.bodd) ≪≫
    FiniteOGP.ofOGPIso _)

private theorem joinMap_dualMap_joinSwap {U U' V V' : Atom} (f : U ⟶ U') (g : V ⟶ V')
    (z : join U.ogp V.ogp) :
    joinMap (dualMap Nat.bodd g) (dualMap Nat.bodd f)
        (joinMap (V.toMoleculeShape.dualIso Nat.bodd).hom (U.toMoleculeShape.dualIso Nat.bodd).hom
          ((joinSwap U.ogp V.ogp).hom z)) =
      joinMap (V'.toMoleculeShape.dualIso Nat.bodd).hom (U'.toMoleculeShape.dualIso Nat.bodd).hom
        ((joinSwap U'.ogp V'.ogp).hom (joinMap f g z)) := by
  obtain ⟨⟨a, b⟩, h⟩ := z
  refine Subtype.ext (Prod.ext ?_ ?_)
  · cases b with
    | none => rfl
    | some y => exact congrArg WithBot.some (congrArg (V'.toMoleculeShape.dualIso Nat.bodd).hom
        (congrArg g (Iso.hom_inv_id_apply (V.toMoleculeShape.dualIso Nat.bodd) y)))
  · cases a with
    | none => rfl
    | some y => exact congrArg WithBot.some (congrArg (U'.toMoleculeShape.dualIso Nat.bodd).hom
        (congrArg f (Iso.hom_inv_id_apply (U.toMoleculeShape.dualIso Nat.bodd) y)))

@[reassoc] theorem dualMap_joinHom_comp_joinDualIso_hom {U U' V V' : Atom} (f : U ⟶ U')
    (g : V ⟶ V') :
    dualMap Nat.bodd (joinHom f g) ≫ (joinDualIso U' V').hom =
      (joinDualIso U V).hom ≫ joinHom (dualMap Nat.bodd g) (dualMap Nat.bodd f) :=
  hom_ext fun x => by
    change (FiniteOGP.ofOGPIso _).hom (joinMap (V'.toMoleculeShape.dualIso Nat.bodd).hom
      (U'.toMoleculeShape.dualIso Nat.bodd).hom ((joinSwap U'.ogp V'.ogp).hom
        ((FiniteOGP.ofOGPIso (join U'.ogp V'.ogp)).inv
          (((atomJoin U' V').toMoleculeShape.dualIso Nat.bodd).inv
            (((atomJoin U' V').toMoleculeShape.dualIso Nat.bodd).hom
              ((FiniteOGP.ofOGPIso (join U'.ogp V'.ogp)).hom (joinMap f g
                ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv
                  (((atomJoin U V).toMoleculeShape.dualIso Nat.bodd).inv x))))))))) =
      (FiniteOGP.ofOGPIso _).hom (joinMap (dualMap Nat.bodd g) (dualMap Nat.bodd f)
        ((FiniteOGP.ofOGPIso _).inv ((FiniteOGP.ofOGPIso _).hom
          (joinMap (V.toMoleculeShape.dualIso Nat.bodd).hom
            (U.toMoleculeShape.dualIso Nat.bodd).hom ((joinSwap U.ogp V.ogp).hom
              ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv
                (((atomJoin U V).toMoleculeShape.dualIso Nat.bodd).inv x)))))))
    rw [Iso.hom_inv_id_apply, joinMap_dualMap_joinSwap]
    refine congrArg (fun w => (FiniteOGP.ofOGPIso _).hom (joinMap _ _ ((joinSwap U'.ogp V'.ogp).hom
      ((FiniteOGP.ofOGPIso (join U'.ogp V'.ogp)).inv w))))
      (Iso.hom_inv_id_apply ((atomJoin U' V').toMoleculeShape.dualIso Nat.bodd) _) |>.trans ?_
    exact congrArg (fun w => (FiniteOGP.ofOGPIso _).hom (joinMap _ _ ((joinSwap U'.ogp V'.ogp).hom
      w))) (Iso.hom_inv_id_apply (FiniteOGP.ofOGPIso (join U'.ogp V'.ogp)) _)

@[reassoc] theorem dualMap_joinInclLeftHom_comp_joinDualIso_hom (U V : Atom) :
    dualMap Nat.bodd (joinInclLeftHom U V) ≫ (joinDualIso U V).hom =
      joinInclRightHom (V.dual Nat.bodd) (U.dual Nat.bodd) :=
  hom_ext fun x => by
    change (FiniteOGP.ofOGPIso _).hom (joinMap (V.toMoleculeShape.dualIso Nat.bodd).hom
      (U.toMoleculeShape.dualIso Nat.bodd).hom ((joinSwap U.ogp V.ogp).hom
        ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv
          (((atomJoin U V).toMoleculeShape.dualIso Nat.bodd).inv
            (((atomJoin U V).toMoleculeShape.dualIso Nat.bodd).hom
              ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).hom (join.inl U.ogp V.ogp
                ((U.toMoleculeShape.dualIso Nat.bodd).inv x)))))))) =
      (FiniteOGP.ofOGPIso _).hom (join.inr _ _ x)
    refine congrArg (fun w => (FiniteOGP.ofOGPIso _).hom (joinMap _ _ ((joinSwap U.ogp V.ogp).hom
      ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv w))))
      (Iso.hom_inv_id_apply ((atomJoin U V).toMoleculeShape.dualIso Nat.bodd) _) |>.trans ?_
    refine congrArg (fun w => (FiniteOGP.ofOGPIso _).hom (joinMap _ _ ((joinSwap U.ogp V.ogp).hom
      w))) (Iso.hom_inv_id_apply (FiniteOGP.ofOGPIso (join U.ogp V.ogp)) _) |>.trans ?_
    exact congrArg (FiniteOGP.ofOGPIso _).hom (Subtype.ext (Prod.ext rfl (congrArg WithBot.some
      (Iso.inv_hom_id_apply (U.toMoleculeShape.dualIso Nat.bodd) x))))

@[reassoc] theorem dualMap_joinInclRightHom_comp_joinDualIso_hom (U V : Atom) :
    dualMap Nat.bodd (joinInclRightHom U V) ≫ (joinDualIso U V).hom =
      joinInclLeftHom (V.dual Nat.bodd) (U.dual Nat.bodd) :=
  hom_ext fun x => by
    change (FiniteOGP.ofOGPIso _).hom (joinMap (V.toMoleculeShape.dualIso Nat.bodd).hom
      (U.toMoleculeShape.dualIso Nat.bodd).hom ((joinSwap U.ogp V.ogp).hom
        ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv
          (((atomJoin U V).toMoleculeShape.dualIso Nat.bodd).inv
            (((atomJoin U V).toMoleculeShape.dualIso Nat.bodd).hom
              ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).hom (join.inr U.ogp V.ogp
                ((V.toMoleculeShape.dualIso Nat.bodd).inv x)))))))) =
      (FiniteOGP.ofOGPIso _).hom (join.inl _ _ x)
    refine congrArg (fun w => (FiniteOGP.ofOGPIso _).hom (joinMap _ _ ((joinSwap U.ogp V.ogp).hom
      ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv w))))
      (Iso.hom_inv_id_apply ((atomJoin U V).toMoleculeShape.dualIso Nat.bodd) _) |>.trans ?_
    refine congrArg (fun w => (FiniteOGP.ofOGPIso _).hom (joinMap _ _ ((joinSwap U.ogp V.ogp).hom
      w))) (Iso.hom_inv_id_apply (FiniteOGP.ofOGPIso (join U.ogp V.ogp)) _) |>.trans ?_
    exact congrArg (FiniteOGP.ofOGPIso _).hom (Subtype.ext (Prod.ext (congrArg WithBot.some
      (Iso.inv_hom_id_apply (V.toMoleculeShape.dualIso Nat.bodd) x)) rfl))

end Atoms.Shape.Atom

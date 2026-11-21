import Atoms.Diagrammatic.RealizationColimits

open CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

def DiagSet.IsRegular (X : DiagSet.{u}) : Prop :=
  ∀ ⦃U : Atom⦄ (x : diagram X U), ¬ IsDegenerate X x →
    Mono (uliftYonedaEquiv.symm x : ball.{u} U ⟶ X)

private theorem mono_uliftYonedaEquiv_symm_iff (X : DiagSet.{u}) {U : Atom} (x : diagram X U) :
    Mono (uliftYonedaEquiv.symm x : ball.{u} U ⟶ X) ↔
      ∀ V : Atom, Function.Injective fun f : V ⟶ U => X.map f.op x := by
  rw [NatTrans.mono_iff_mono_app]
  constructor
  · intro h V f g hfg
    exact ULift.up_inj.1 ((mono_iff_injective _).1 (h (op V))
      (a₁ := ULift.up f) (a₂ := ULift.up g) (by simpa using hfg))
  · rintro h ⟨V⟩
    rw [mono_iff_injective]
    rintro ⟨f⟩ ⟨g⟩ hfg
    exact congrArg ULift.up (h V (by simpa using hfg))

theorem DiagSet.IsRegular.injective_map {X : DiagSet.{u}} (hX : X.IsRegular) {U : Atom}
    (x : diagram X U) (hx : ¬ IsDegenerate X x) (V : Atom) :
    Function.Injective fun f : V ⟶ U => X.map f.op x :=
  (mono_uliftYonedaEquiv_symm_iff X x).1 (hX x hx) V

theorem DiagSet.IsRegular.not_isDegenerate_map {X : DiagSet.{u}} (hX : X.IsRegular)
    {U V : Atom} (x : diagram X U) (hx : ¬ IsDegenerate X x) (ι : V ⟶ U)
    (hι : IsInclusionHom ι) : ¬ IsDegenerate X (X.map ι.op x) := by
  rintro ⟨W, p, y, hp, hnp, hy⟩
  have := isSplitEpi_of_isCollapseHom p hp
  have := mono_of_isInclusionHom ι hι
  have h : (p ≫ section_ p) ≫ ι = 𝟙 V ≫ ι := hX.injective_map x hx V (by
    dsimp only
    rw [Category.id_comp, op_comp, Functor.map_comp_apply, ← hy, ← Functor.map_comp_apply,
      ← op_comp, Category.assoc, IsSplitEpi.id, Category.comp_id])
  exact hnp ⟨section_ p, (cancel_mono ι).1 h, IsSplitEpi.id p⟩

theorem DiagSet.IsRegular.of_mono {X Y : DiagSet.{u}} (m : X ⟶ Y) [Mono m]
    (hY : Y.IsRegular) : X.IsRegular := by
  intro U x hx
  refine (mono_uliftYonedaEquiv_symm_iff X x).2 fun V f g hfg => ?_
  refine hY.injective_map (m.app (op U) x) (fun h => hx (isDegenerate_of_isDegenerate_app m h)) V ?_
  simp only [← NatTrans.naturality_apply]
  exact congrArg (m.app (op V)) hfg

theorem DiagSet.IsRegular.of_iso {X Y : DiagSet.{u}} (e : X ≅ Y) (hX : X.IsRegular) :
    Y.IsRegular :=
  hX.of_mono e.inv

private theorem injective_of_not_isDegenerate_realize (P : RDCpx.{0}) {U : Atom}
    (c : atomToRDCpx.obj U ⟶ P) (hc : ¬ IsDegenerate (realize.{u}.obj P) ⟨c⟩) :
    Function.Injective (ConcreteCategory.hom c.hom) := by
  classical
  let _ (y : P.obj.toOGP) : FinEnum (P.obj.toOGP.restrict (.Iic y)) :=
    have : Fintype (P.obj.toOGP.restrict (.Iic y)) := (IsMoleculeIn.finite (P.obj.isRDC y)).fintype
    FinEnum.ofEquiv _ (Fintype.equivFin _)
  set t := ConcreteCategory.hom c.hom U.top
  set L := principalLiftRDC P t c (hom_apply_mem_closure_apply_top c)
  have hL : atomToRDCpx.map L ≫ principalInclusionRDC P t = c :=
    principalLiftRDC_comp_principalInclusionRDC P t c _
  have htop : L U.top = (principalAtomRDC P t).top := injective_principalInclusionRDC P t (by
    rw [principalInclusionRDC_top]
    exact congrArg (fun f : atomToRDCpx.obj U ⟶ P => ConcreteCategory.hom f.hom U.top) hL)
  have hiso : IsIso L := by
    by_contra hni
    refine hc ⟨_, L, ⟨principalInclusionRDC P t⟩, isCollapseHom_of_apply_eq_top L htop, hni, ?_⟩
    rw [realize_obj_map, hL]
  have hinj : Function.Injective L :=
    Function.LeftInverse.injective (ConcreteCategory.congr_hom (IsIso.hom_inv_id L))
  rw [← hL]
  exact (injective_principalInclusionRDC P t).comp hinj

theorem isRegular_realize (P : RDCpx.{0}) : (realize.{u}.obj P).IsRegular := by
  rintro U ⟨c⟩ hc
  refine (mono_uliftYonedaEquiv_symm_iff _ _).2 fun V f g hfg => ?_
  have hfg' : atomToRDCpx.map f ≫ c = atomToRDCpx.map g ≫ c := ULift.up_inj.1 hfg
  exact Atom.hom_ext fun v => injective_of_not_isDegenerate_realize P c hc
    (congrArg (fun k : atomToRDCpx.obj V ⟶ P => ConcreteCategory.hom k.hom v) hfg')

end Atoms.Diagrammatic

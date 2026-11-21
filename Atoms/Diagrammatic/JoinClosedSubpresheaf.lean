import Atoms.Diagrammatic.ClosedSubpresheafPushout
import Atoms.Diagrammatic.Join
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

open CategoryTheory CategoryTheory.WithInitial MonoidalCategory Limits Opposite Atoms.Shape
  Atoms.Molecule
open scoped MonoidalCategory.DayConvolution

universe u

namespace Atoms.Diagrammatic

open scoped DiagSet.Join

section Cells

variable {U : Atom} (A : LowerSet U.ogp)

private abbrev augSub : AugmentedAtomᵒᵖ ⥤ Type u :=
  trivialAugmentation.obj (closedSubpresheaf.{u} U A).toFunctor

private def augHom {x : AugmentedAtomᵒᵖ} (s : (augSub.{u} A).obj x) : x.unop ⟶ of U :=
  ((trivialAugmentationULiftYonedaIso U).hom.app x
    ((trivialAugmentation.map (closedSubpresheaf.{u} U A).ι).app x s)).down

private theorem augHom_map {x y : AugmentedAtomᵒᵖ} (p : x ⟶ y) (s : (augSub.{u} A).obj x) :
    augHom A ((augSub A).map p s) = p.unop ≫ augHom A s :=
  congrArg ULift.down (NatTrans.naturality_apply
    (trivialAugmentation.map (closedSubpresheaf.{u} U A).ι ≫
      (trivialAugmentationULiftYonedaIso U).hom) p s)

private theorem augHom_injective (x : AugmentedAtomᵒᵖ) :
    Function.Injective (augHom.{u} A (x := x)) := by
  obtain ⟨x⟩ := x
  cases x with
  | star => exact fun _ _ _ => Subsingleton.elim _ _
  | of X => exact fun s s' h => Subtype.ext (ULift.ext _ _ h)

private theorem augHom_mem {x : AugmentedAtomᵒᵖ} (s : (augSub.{u} A).obj x)
    (z : augmentedCarrier.obj x.unop) (a : U.ogp)
    (h : augmentedCarrier.map (augHom A s) z = (a : WithBot U.ogp)) : a ∈ A := by
  obtain ⟨x⟩ := x
  cases x with
  | star => exact absurd h WithBot.bot_ne_coe
  | of X =>
    induction z using WithBot.recBotCoe with
    | bot => exact absurd h WithBot.bot_ne_coe
    | coe t => exact WithBot.coe_injective h ▸ s.2 t

private theorem exists_augHom_eq_closureIncl (a : WithBot U.ogp)
    (ha : ∀ b : U.ogp, a = b → b ∈ A) :
    ∃ s : (augSub.{u} A).obj (op (AugmentedAtom.closure U a)),
      augHom A s = AugmentedAtom.closureIncl U a := by
  induction a using WithBot.recBotCoe with
  | bot => exact ⟨PUnit.unit, starInitial.hom_ext _ _⟩
  | coe x => exact ⟨⟨ULift.up (Atom.closureIncl U x),
      fun t => A.lower (closureIncl_mem_closure U x t) (ha x rfl)⟩, rfl⟩

end Cells

section Join

variable {U V : Atom} (A : LowerSet U.ogp) (B : LowerSet V.ogp)

private noncomputable def joinCompare :
    WithInitial.join (closedSubpresheaf.{u} U A).toFunctor (closedSubpresheaf.{u} V B).toFunctor ⟶
      ball.{u} (atomJoin U V) :=
  WithInitial.joinMap (closedSubpresheaf U A).ι (closedSubpresheaf V B).ι ≫ (joinBallIso U V).hom

private theorem joinCompare_app_map_unit {T : Atom} {x y : AugmentedAtomᵒᵖ}
    (w : x ⊗ y ⟶ op (of T)) (s : (augSub.{u} A).obj x) (t : (augSub.{u} B).obj y) :
    (joinCompare A B).app (op T) ((augSub A ⊛ augSub B).map w
      ((DayConvolution.unit (augSub A) (augSub B)).app (x, y) (s, t))) =
      ULift.up (w.unop ≫ (augHom A s ⊗ₘ augHom B t)) := by
  have h1 := DayConvolution.map_comp (trivialAugmentation.map (closedSubpresheaf.{u} U A).ι)
    (trivialAugmentationULiftYonedaIso U).hom
    (trivialAugmentation.map (closedSubpresheaf.{u} V B).ι)
    (trivialAugmentationULiftYonedaIso V).hom
  have h2 := congrArg (fun k => (DayConvolution.uliftYonedaIso (of U) (of V)).hom.app (op (of T))
    (k.app (op (of T)) ((augSub A ⊛ augSub B).map w
      ((DayConvolution.unit (augSub A) (augSub B)).app (x, y) (s, t))))) h1
  refine h2.symm.trans ?_
  have h3 := ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app
    (trivialAugmentation.map (closedSubpresheaf.{u} U A).ι ≫
      (trivialAugmentationULiftYonedaIso U).hom)
    (trivialAugmentation.map (closedSubpresheaf.{u} V B).ι ≫
      (trivialAugmentationULiftYonedaIso V).hom)
    x y) ((s, t) : (augSub A).obj x × (augSub B).obj y)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h3
  rw [NatTrans.naturality_apply, h3, NatTrans.naturality_apply]
  refine (congrArg _ (DayConvolution.uliftYonedaIso_hom_app_unit_app (of U) (of V)
    (augHom A s) (augHom B t))).trans ?_
  rfl

private theorem map_tensorHom_unit_app (P Q : AugmentedAtomᵒᵖ ⥤ Type u)
    {x x' y y' : AugmentedAtomᵒᵖ}
    (f : x ⟶ x') (g : y ⟶ y') (a : P.obj x) (b : Q.obj y) :
    (P ⊛ Q).map (f ⊗ₘ g) ((DayConvolution.unit P Q).app (x, y) (a, b)) =
      (DayConvolution.unit P Q).app (x', y') (P.map f a, Q.map g b) :=
  (NatTrans.naturality_apply (DayConvolution.unit P Q) (X := (x, y)) (Y := (x', y')) (f, g)
    ((a, b) : P.obj x × Q.obj y)).symm

private theorem joinCompare_app_mem {T : Atom}
    (e : (WithInitial.join (closedSubpresheaf.{u} U A).toFunctor
      (closedSubpresheaf.{u} V B).toFunctor).obj (op T)) :
    (joinCompare A B).app (op T) e ∈
      (closedSubpresheaf.{u} (atomJoin U V) (closedJoin A B)).obj (op T) := by
  obtain ⟨x, y, w, s, t, rfl⟩ :=
    DayConvolution.map_unit_app_jointly_surjective (augSub A) (augSub B) (c := op (of T)) e
  rw [joinCompare_app_map_unit]
  intro r
  have hr := Functor.map_comp_apply augmentedCarrier w.unop
    (augHom A s ⊗ₘ augHom B t) (r : WithBot T.ogp)
  rw [AugmentedAtom.augmentedCarrier_map_tensorHom_apply] at hr
  refine mem_closedJoin.2 ⟨fun a ha => augHom_mem A s
    ((augmentedCarrierμIso _ _).inv (augmentedCarrier.map w.unop (r : WithBot T.ogp))).1 a ?_,
    fun b hb => augHom_mem B t
      ((augmentedCarrierμIso _ _).inv (augmentedCarrier.map w.unop (r : WithBot T.ogp))).2 b ?_⟩
  · exact (atomJoinFst_atomJoinPair _ _).symm.trans ((congrArg atomJoinFst hr).symm.trans ha)
  · exact (atomJoinSnd_atomJoinPair _ _).symm.trans ((congrArg atomJoinSnd hr).symm.trans hb)

private theorem exists_eq_map_of_augHom {x : AugmentedAtomᵒᵖ} (s : (augSub.{u} A).obj x) :
    ∃ (a : WithBot U.ogp) (p : x.unop ⟶ AugmentedAtom.closure U a)
      (c : (augSub.{u} A).obj (op (AugmentedAtom.closure U a))),
      augHom A c = AugmentedAtom.closureIncl U a ∧ s = (augSub A).map p.op c := by
  obtain ⟨a, p, ⟨z, hz⟩, hp⟩ := AugmentedAtom.exists_comp_closureIncl_eq (augHom A s)
  obtain ⟨c, hc⟩ := exists_augHom_eq_closureIncl A a fun b hb => augHom_mem A s z b (hz.trans hb)
  exact ⟨a, p, c, hc, augHom_injective A x ((augHom_map A p.op c).trans
    ((congrArg (p ≫ ·) hc).trans hp)).symm⟩

private theorem atomJoinFst_le {T : Atom} {a : WithBot U.ogp} {b : WithBot V.ogp}
    (w : of T ⟶ AugmentedAtom.closure U a ⊗ AugmentedAtom.closure V b)
    (z : augmentedCarrier.obj (of T)) :
    atomJoinFst (augmentedCarrier.map
      (w ≫ (AugmentedAtom.closureIncl U a ⊗ₘ AugmentedAtom.closureIncl V b)) z) ≤ a := by
  rw [Functor.map_comp_apply, AugmentedAtom.augmentedCarrier_map_tensorHom_apply]
  refine (atomJoinFst_atomJoinPair _ _).trans_le ?_
  exact (AugmentedAtom.range_augmentedCarrier_map_closureIncl U a).le ⟨_, rfl⟩

private theorem atomJoinSnd_le {T : Atom} {a : WithBot U.ogp} {b : WithBot V.ogp}
    (w : of T ⟶ AugmentedAtom.closure U a ⊗ AugmentedAtom.closure V b)
    (z : augmentedCarrier.obj (of T)) :
    atomJoinSnd (augmentedCarrier.map
      (w ≫ (AugmentedAtom.closureIncl U a ⊗ₘ AugmentedAtom.closureIncl V b)) z) ≤ b := by
  rw [Functor.map_comp_apply, AugmentedAtom.augmentedCarrier_map_tensorHom_apply]
  refine (atomJoinSnd_atomJoinPair _ _).trans_le ?_
  exact (AugmentedAtom.range_augmentedCarrier_map_closureIncl V b).le ⟨_, rfl⟩

private theorem exists_comp_closureIncl_eq_closureIncl {a a' : WithBot U.ogp} (h : a' ≤ a) :
    ∃ p : AugmentedAtom.closure U a' ⟶ AugmentedAtom.closure U a,
      p ≫ AugmentedAtom.closureIncl U a = AugmentedAtom.closureIncl U a' :=
  AugmentedAtom.exists_comp_eq_of_range_subset _
    (AugmentedAtom.injective_augmentedCarrier_map_closureIncl U a) _ (by
      rw [AugmentedAtom.range_augmentedCarrier_map_closureIncl,
        AugmentedAtom.range_augmentedCarrier_map_closureIncl]
      exact Set.Iic_subset_Iic.2 h)

private theorem eq_map_unit_app_of_joinCompare_app_eq {T : Atom}
    (e : (WithInitial.join (closedSubpresheaf.{u} U A).toFunctor
      (closedSubpresheaf.{u} V B).toFunctor).obj (op T))
    {g : T ⟶ atomJoin U V} (hg : (joinCompare A B).app (op T) e = ULift.up g)
    {a₁ : WithBot U.ogp} {b₁ : WithBot V.ogp}
    (ha₁ : atomJoinFst (g T.top : WithBot (atomJoin U V).ogp) = a₁)
    (hb₁ : atomJoinSnd (g T.top : WithBot (atomJoin U V).ogp) = b₁)
    (v : of T ⟶ AugmentedAtom.closure U a₁ ⊗ AugmentedAtom.closure V b₁)
    (hv : v ≫ (AugmentedAtom.closureIncl U a₁ ⊗ₘ AugmentedAtom.closureIncl V b₁) =
      WithInitial.incl.map g)
    (sa : (augSub.{u} A).obj (op (AugmentedAtom.closure U a₁)))
    (hsa : augHom A sa = AugmentedAtom.closureIncl U a₁)
    (sb : (augSub.{u} B).obj (op (AugmentedAtom.closure V b₁)))
    (hsb : augHom B sb = AugmentedAtom.closureIncl V b₁) :
    e = (augSub A ⊛ augSub B).map v.op
      ((DayConvolution.unit (augSub A) (augSub B)).app (op _, op _) (sa, sb)) := by
  obtain ⟨x, y, w, s, t, rfl⟩ := DayConvolution.map_unit_app_jointly_surjective
    (augSub.{u} A) (augSub.{u} B) (c := op (of T)) e
  obtain ⟨a, p, c, hc, rfl⟩ := exists_eq_map_of_augHom A s
  obtain ⟨b, q, d, hd, rfl⟩ := exists_eq_map_of_augHom B t
  rw [joinCompare_app_map_unit, augHom_map, augHom_map, hc, hd] at hg
  have hw : (w.unop ≫ (p ⊗ₘ q)) ≫
      (AugmentedAtom.closureIncl U a ⊗ₘ AugmentedAtom.closureIncl V b) = WithInitial.incl.map g :=
    (Category.assoc _ _ _).trans ((congrArg (w.unop ≫ ·) (tensorHom_comp_tensorHom _ _ _ _)).trans
      (congrArg ULift.down hg))
  have ha : a₁ ≤ a := by
    have h := atomJoinFst_le (w.unop ≫ (p ⊗ₘ q)) (T.top : WithBot T.ogp)
    rw [hw] at h
    exact ha₁ ▸ h
  have hb : b₁ ≤ b := by
    have h := atomJoinSnd_le (w.unop ≫ (p ⊗ₘ q)) (T.top : WithBot T.ogp)
    rw [hw] at h
    exact hb₁ ▸ h
  obtain ⟨pm, hpm⟩ := exists_comp_closureIncl_eq_closureIncl ha
  obtain ⟨qm, hqm⟩ := exists_comp_closureIncl_eq_closureIncl hb
  have hw' : w.unop ≫ (p ⊗ₘ q) = v ≫ (pm ⊗ₘ qm) :=
    (cancel_mono (AugmentedAtom.closureIncl U a ⊗ₘ AugmentedAtom.closureIncl V b)).1
      (hw.trans (hv.symm.trans (by rw [Category.assoc, tensorHom_comp_tensorHom, hpm, hqm])))
  have hsa' : (augSub A).map pm.op c = sa :=
    augHom_injective A _ ((augHom_map A pm.op c).trans ((congrArg (pm ≫ ·) hc).trans
      (hpm.trans hsa.symm)))
  have hsb' : (augSub B).map qm.op d = sb :=
    augHom_injective B _ ((augHom_map B qm.op d).trans ((congrArg (qm ≫ ·) hd).trans
      (hqm.trans hsb.symm)))
  have hw'' : (p.op ⊗ₘ q.op) ≫ w = (pm.op ⊗ₘ qm.op) ≫ v.op := Quiver.Hom.unop_inj hw'
  rw [← map_tensorHom_unit_app, ← Functor.map_comp_apply, hw'', Functor.map_comp_apply,
    map_tensorHom_unit_app, hsa', hsb']
  rfl

private theorem joinCompare_app_injective (T : Atom) :
    Function.Injective ((joinCompare.{u} A B).app (op T)) := by
  intro e e' h
  obtain ⟨g, hg⟩ : ∃ g : T ⟶ atomJoin U V,
    (joinCompare.{u} A B).app (op T) e = ULift.up g := ⟨_, rfl⟩
  have hm : g T.top ∈ closedJoin A B := by
    have := joinCompare_app_mem A B e
    rw [hg] at this
    exact this T.top
  obtain ⟨a, ha⟩ : ∃ a, atomJoinFst (g T.top : WithBot (atomJoin U V).ogp) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, atomJoinSnd (g T.top : WithBot (atomJoin U V).ogp) = b := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := AugmentedAtom.exists_comp_tensorHom_closureIncl_eq g ha.le hb.le
  obtain ⟨sa, hsa⟩ := exists_augHom_eq_closureIncl A a (ha ▸ hm.1)
  obtain ⟨sb, hsb⟩ := exists_augHom_eq_closureIncl B b (hb ▸ hm.2)
  exact (eq_map_unit_app_of_joinCompare_app_eq A B e hg ha hb v hv sa hsa sb hsb).trans
    (eq_map_unit_app_of_joinCompare_app_eq A B e' (h.symm.trans hg) ha hb v hv sa hsa sb
      hsb).symm

private theorem exists_joinCompare_app_eq {T : Atom} (g : T ⟶ atomJoin U V)
    (hg : ∀ t, g t ∈ closedJoin A B) :
    ∃ e, (joinCompare.{u} A B).app (op T) e = ULift.up g := by
  have hm := mem_closedJoin.1 (hg T.top)
  obtain ⟨a, ha⟩ : ∃ a, atomJoinFst (g T.top : WithBot (atomJoin U V).ogp) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, atomJoinSnd (g T.top : WithBot (atomJoin U V).ogp) = b := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := AugmentedAtom.exists_comp_tensorHom_closureIncl_eq g ha.le hb.le
  obtain ⟨sa, hsa⟩ := exists_augHom_eq_closureIncl A a (ha ▸ hm.1)
  obtain ⟨sb, hsb⟩ := exists_augHom_eq_closureIncl B b (hb ▸ hm.2)
  refine ⟨(augSub.{u} A ⊛ augSub.{u} B).map v.op
    ((DayConvolution.unit (augSub.{u} A) (augSub.{u} B)).app (op _, op _) (sa, sb)), ?_⟩
  exact (joinCompare_app_map_unit A B v.op sa sb).trans (congrArg ULift.up
    ((congrArg₂ (fun f g => v ≫ (f ⊗ₘ g)) hsa hsb).trans hv))

private noncomputable def joinCompareLift :
    WithInitial.join (closedSubpresheaf.{u} U A).toFunctor (closedSubpresheaf.{u} V B).toFunctor ⟶
      (closedSubpresheaf.{u} (atomJoin U V) (closedJoin A B)).toFunctor :=
  Subfunctor.lift (joinCompare.{u} A B) (by
    rintro T _ ⟨e, rfl⟩
    exact joinCompare_app_mem.{u} A B (T := T.unop) e)

private instance : IsIso (joinCompareLift.{u} A B) := by
  have (T : Atomᵒᵖ) : IsIso ((joinCompareLift.{u} A B).app T) := by
    refine (isIso_iff_bijective _).2 ⟨fun e e' h =>
      joinCompare_app_injective A B T.unop (congrArg Subtype.val h), fun ⟨⟨g⟩, hg⟩ => ?_⟩
    obtain ⟨e, he⟩ := exists_joinCompare_app_eq A B g hg
    exact ⟨e, Subtype.ext he⟩
  exact NatIso.isIso_of_isIso_app _

end Join

section Iso

variable {U V : Atom}

noncomputable def joinClosedSubpresheafIso {U V : Atom} (A : LowerSet U.ogp)
    (B : LowerSet V.ogp) :
    WithInitial.join (closedSubpresheaf.{u} U A).toFunctor (closedSubpresheaf.{u} V B).toFunctor ≅
      (closedSubpresheaf.{u} (atomJoin U V) (closedJoin A B)).toFunctor :=
  asIso (joinCompareLift A B)

@[reassoc] theorem joinClosedSubpresheafIso_hom_comp_ι {U V : Atom} (A : LowerSet U.ogp)
    (B : LowerSet V.ogp) :
    (joinClosedSubpresheafIso.{u} A B).hom ≫ (closedSubpresheaf (atomJoin U V) (closedJoin A B)).ι =
      WithInitial.joinMap (closedSubpresheaf U A).ι (closedSubpresheaf V B).ι ≫
        (joinBallIso U V).hom :=
  rfl

instance mono_joinMap_closedSubpresheaf_ι {U V : Atom} (A : LowerSet U.ogp)
    (B : LowerSet V.ogp) :
    Mono (WithInitial.joinMap (closedSubpresheaf.{u} U A).ι (closedSubpresheaf.{u} V B).ι) :=
  have : Mono (WithInitial.joinMap (closedSubpresheaf.{u} U A).ι (closedSubpresheaf.{u} V B).ι ≫
      (joinBallIso U V).hom) := by
    rw [← joinClosedSubpresheafIso_hom_comp_ι]
    infer_instance
  mono_of_mono _ (joinBallIso U V).hom

end Iso

section Leibniz

variable {U V : Atom}

private theorem joinMap_comp_joinClosedSubpresheafIso_hom {A A' : LowerSet U.ogp}
    {B B' : LowerSet V.ogp}
    (f : (closedSubpresheaf.{u} U A).toFunctor ⟶ (closedSubpresheaf.{u} U A').toFunctor)
    (g : (closedSubpresheaf.{u} V B).toFunctor ⟶ (closedSubpresheaf.{u} V B').toFunctor)
    (k : (closedSubpresheaf.{u} (atomJoin U V) (closedJoin A B)).toFunctor ⟶
      (closedSubpresheaf.{u} (atomJoin U V) (closedJoin A' B')).toFunctor)
    (hf : f ≫ (closedSubpresheaf U A').ι = (closedSubpresheaf U A).ι)
    (hg : g ≫ (closedSubpresheaf V B').ι = (closedSubpresheaf V B).ι)
    (hk : k ≫ (closedSubpresheaf (atomJoin U V) (closedJoin A' B')).ι =
      (closedSubpresheaf (atomJoin U V) (closedJoin A B)).ι) :
    WithInitial.joinMap f g ≫ (joinClosedSubpresheafIso A' B').hom =
      (joinClosedSubpresheafIso A B).hom ≫ k := by
  rw [← cancel_mono (closedSubpresheaf (atomJoin U V) (closedJoin A' B')).ι, Category.assoc,
    joinClosedSubpresheafIso_hom_comp_ι, Category.assoc, hk, joinClosedSubpresheafIso_hom_comp_ι,
    ← Category.assoc, joinMap_comp_joinMap, hf, hg]

noncomputable def pushoutObjObjClosedSubpresheafArrowIso {A A' : LowerSet U.ogp}
    {B B' : LowerSet V.ogp} (hA : A ≤ A') (hB : B ≤ B') :
    Arrow.mk (Functor.PushoutObjObj.ofHasPushout 𝒥
      (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} U hA))
      (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} V hB))).ι ≅
      Arrow.mk (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} (atomJoin U V)
        (sup_le (closedJoin_mono le_rfl hB) (closedJoin_mono hA le_rfl) :
          closedJoin A' B ⊔ closedJoin A B' ≤ closedJoin A' B'))) := by
  have hi : closedJoin A' B ⊓ closedJoin A B' = closedJoin A B := by
    rw [closedJoin_inf, inf_eq_right.2 hA, inf_eq_left.2 hB]
  let e : (closedSubpresheaf.{u} (atomJoin U V) (closedJoin A B)).toFunctor ≅
      (closedSubpresheaf.{u} (atomJoin U V) (closedJoin A' B ⊓ closedJoin A B')).toFunctor :=
    { hom := Subfunctor.homOfLe (closedSubpresheaf_mono _ hi.ge)
      inv := Subfunctor.homOfLe (closedSubpresheaf_mono _ hi.le) }
  have P := (isPushout_closedSubpresheaf.{u} (atomJoin U V) (closedJoin A' B)
    (closedJoin A B')).of_iso' (joinClosedSubpresheafIso A B ≪≫ e)
    (joinClosedSubpresheafIso A' B) (joinClosedSubpresheafIso A B') (Iso.refl _)
    (f' := WithInitial.joinMap (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} U hA)) (𝟙 _))
    (g' := WithInitial.joinMap (𝟙 _) (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} V hB)))
    (inl' := (joinClosedSubpresheafIso A' B).hom ≫
      Subfunctor.homOfLe (closedSubpresheaf_mono _ le_sup_left))
    (inr' := (joinClosedSubpresheafIso A B').hom ≫
      Subfunctor.homOfLe (closedSubpresheaf_mono _ le_sup_right))
    ((Category.assoc _ _ _).trans (joinMap_comp_joinClosedSubpresheafIso_hom _ _
      (Subfunctor.homOfLe (closedSubpresheaf_mono _ (closedJoin_mono hA le_rfl))) (by simp)
      (by simp) (by simp)).symm)
    ((Category.assoc _ _ _).trans (joinMap_comp_joinClosedSubpresheafIso_hom _ _
      (Subfunctor.homOfLe (closedSubpresheaf_mono _ (closedJoin_mono le_rfl hB))) (by simp)
      (by simp) (by simp)).symm)
    (Category.comp_id _).symm (Category.comp_id _).symm
  let sq := Functor.PushoutObjObj.ofHasPushout 𝒥
    (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} U hA))
    (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} V hB))
  refine Arrow.isoMk (sq.isPushout.isoIsPushout _ _ P) (joinClosedSubpresheafIso A' B') ?_
  refine sq.hom_ext ?_ ?_
  · refine (IsPushout.inl_isoIsPushout_hom_assoc _ _ sq.isPushout P _).trans ?_
    refine Eq.trans ?_ (sq.inl_ι_assoc _).symm
    exact ((Category.assoc _ _ _).trans (congrArg _ rfl)).trans
      (joinMap_comp_joinClosedSubpresheafIso_hom _ _
        (Subfunctor.homOfLe (closedSubpresheaf_mono _ (closedJoin_mono le_rfl hB))) (by simp)
        (by simp) (by simp)).symm
  · refine (IsPushout.inr_isoIsPushout_hom_assoc _ _ sq.isPushout P _).trans ?_
    refine Eq.trans ?_ (sq.inr_ι_assoc _).symm
    exact ((Category.assoc _ _ _).trans (congrArg _ rfl)).trans
      (joinMap_comp_joinClosedSubpresheafIso_hom _ _
        (Subfunctor.homOfLe (closedSubpresheaf_mono _ (closedJoin_mono hA le_rfl))) (by simp)
        (by simp) (by simp)).symm

theorem pushoutObjObjClosedSubpresheafArrowIso_hom_right {A A' : LowerSet U.ogp}
    {B B' : LowerSet V.ogp} (hA : A ≤ A') (hB : B ≤ B') :
    (pushoutObjObjClosedSubpresheafArrowIso.{u} hA hB).hom.right =
      (joinClosedSubpresheafIso A' B').hom :=
  rfl

end Leibniz

section Sphere

private def ιArrowIsoOfEq {X : DiagSet.{u}} {G G' : Subfunctor X} (h : G = G') :
    Arrow.mk G.ι ≅ Arrow.mk G'.ι := by
  subst h
  exact Iso.refl _

private def homOfLeArrowIsoOfEq {X : DiagSet.{u}} {G H G' H' : Subfunctor X} (h : G ≤ H)
    (h' : G' ≤ H') (hG : G = G') (hH : H = H') :
    Arrow.mk (Subfunctor.homOfLe h) ≅ Arrow.mk (Subfunctor.homOfLe h') := by
  subst hG hH
  exact Iso.refl _

private noncomputable def sphereInclusionArrowIso (U : Atom) :
    Arrow.mk (sphereInclusion.{u} U) ≅
      Arrow.mk (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} U
        (le_top : U.ogp.bdryFull ⊤ ≤ ⊤))) :=
  (ιArrowIsoOfEq (closedSubpresheaf_univ_erase_top U)).symm ≪≫
    (homOfLeUnivArrowIso U (U.ogp.bdryFull ⊤)).symm

noncomputable def pushoutObjObjSphereInclusionArrowIso (U V : Atom) :
    Arrow.mk (Functor.PushoutObjObj.ofHasPushout 𝒥
      (sphereInclusion.{u} U) (sphereInclusion.{u} V)).ι ≅
      Arrow.mk (sphereInclusion.{u} (atomJoin U V)) := by
  have h₁ : closedJoin (⊤ : LowerSet U.ogp) (V.ogp.bdryFull ⊤) ⊔
      closedJoin (U.ogp.bdryFull ⊤) (⊤ : LowerSet V.ogp) = (atomJoin U V).ogp.bdryFull ⊤ :=
    (sup_comm _ _).trans (bdryFull_atomJoin U V).symm
  have e₁ := Functor.PushoutObjObj.ι_iso_of_iso_left (f₂ := Arrow.mk (sphereInclusion.{u} V))
    (Functor.PushoutObjObj.ofHasPushout 𝒥 (sphereInclusion.{u} U) (sphereInclusion.{u} V))
    (Functor.PushoutObjObj.ofHasPushout _ _ _) (sphereInclusionArrowIso U)
  have e₂ := Functor.PushoutObjObj.ι_iso_of_iso_right
    (f₁ := Arrow.mk (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} U
      (le_top : U.ogp.bdryFull ⊤ ≤ ⊤))))
    (Functor.PushoutObjObj.ofHasPushout 𝒥 (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} U
      (le_top : U.ogp.bdryFull ⊤ ≤ ⊤))) (sphereInclusion.{u} V))
    (Functor.PushoutObjObj.ofHasPushout _ _ _) (sphereInclusionArrowIso V)
  have e₃ := pushoutObjObjClosedSubpresheafArrowIso.{u}
    (le_top : U.ogp.bdryFull ⊤ ≤ ⊤) (le_top : V.ogp.bdryFull ⊤ ≤ ⊤)
  have e₄ := homOfLeArrowIsoOfEq.{u} (closedSubpresheaf_mono.{u} (atomJoin U V)
    (sup_le (closedJoin_mono le_rfl le_top) (closedJoin_mono le_top le_rfl) :
      closedJoin ⊤ (V.ogp.bdryFull ⊤) ⊔ closedJoin (U.ogp.bdryFull ⊤) ⊤ ≤ closedJoin ⊤ ⊤))
    (closedSubpresheaf_mono.{u} (atomJoin U V)
    (le_top : (atomJoin U V).ogp.bdryFull ⊤ ≤ ⊤)) (congrArg _ h₁) (congrArg _ closedJoin_top_top)
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ (sphereInclusionArrowIso (atomJoin U V)).symm

end Sphere

end Atoms.Diagrammatic

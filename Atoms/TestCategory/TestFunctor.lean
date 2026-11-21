import Atoms.ForMathlib.CategoryTheory.Elements
import Atoms.TestCategory.BasicLocalizer.Homotopy
import Atoms.TestCategory.Presheaf.Transport
import Atoms.TestCategory.SeparatingIntervalCriterion

open CategoryTheory Limits MonoidalCategory MorphismProperty Opposite

namespace Atoms.TestCategory

open Homotopical (SeparatingInterval)

universe u

variable {A : Type u} [SmallCategory A] (i : A ⥤ Cat.{u, u})

noncomputable def evalTerminalHom [∀ a, HasTerminal (i.obj a)] (C : Cat.{u, u}) :
    (elementsFunctor A).obj (i.nerve C) ⟶ C :=
  Cat.Hom.ofFunctor (Functor.nerveEvalTerminal (fun _ => terminalIsTerminal) C)

theorem elementsFunctor_map_nerveMap_comp_evalTerminalHom [∀ a, HasTerminal (i.obj a)]
    {C D : Cat.{u, u}} (F : C ⟶ D) :
    (elementsFunctor A).map (i.nerveMap F.toFunctor) ≫ evalTerminalHom i D =
      evalTerminalHom i C ≫ F :=
  Cat.Hom.ext
    (Functor.nerveEvalTerminal_comp (D := i) (fun _ => terminalIsTerminal) C F.toFunctor).symm

namespace BasicLocalizer

variable (𝒲 : BasicLocalizer.{u})

structure IsLocalTestFunctor : Prop where
  isLocalTest : 𝒲.IsLocalTest A
  aspherical_obj (a : A) : 𝒲.Aspherical (i.obj a)
  locallyAspherical_nerve (C : Cat.{u, u}) : 𝒲.Aspherical C → 𝒲.LocallyAspherical A (i.nerve C)

structure IsTestFunctor : Prop extends 𝒲.IsLocalTestFunctor i where
  isTest : 𝒲.IsTest A

theorem pshAspherical_over_iff (a : A) (X : Aᵒᵖ ⥤ Type u) :
    𝒲.PshAspherical (Over a) ((Over.forget a).op ⋙ X) ↔ 𝒲.PshAspherical A (yoneda.obj a ⨯ X) := by
  rw [𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)]
  let e := elementsOverRestrictEquivalence A a X
  exact ⟨𝒲.aspherical_of_equivalence e, 𝒲.aspherical_of_equivalence e.symm⟩

theorem pshAspherical_of_locallyAspherical (hA : 𝒲.Aspherical (Cat.of A)) {X : Aᵒᵖ ⥤ Type u}
    (hX : 𝒲.LocallyAspherical A X) : 𝒲.PshAspherical A X := by
  have hT : 𝒲.PshAspherical A (⊤_ (Aᵒᵖ ⥤ Type u)) := by
    rw [𝒲.pshAspherical_iff_wPsh_terminal_from A hA, terminal.hom_ext (terminal.from _) (𝟙 _)]
    exact (𝒲.wPsh A).id_mem _
  have h := (𝒲.aspherical_iff_of_W _ (𝒲.wPsh_snd_of_locallyAspherical A hX _)).2 hT
  refine (𝒲.pshAspherical_iff_of_iso A ?_).1 h
  exact
    { hom := CartesianMonoidalCategory.fst _ _
      inv := CartesianMonoidalCategory.lift (𝟙 X) (terminal.from X)
      hom_inv_id := CartesianMonoidalCategory.hom_ext _ _ (by simp) (terminal.hom_ext _ _) }

theorem asphericalFunctor_nerveEvalTerminal {B : Type u} [SmallCategory B] {j : B ⥤ Cat.{u, u}}
    {t : ∀ b, j.obj b} (ht : ∀ b, IsTerminal (t b)) (C : Cat.{u, u})
    (h : ∀ c : C, 𝒲.PshAspherical B (j.nerve (Over c))) :
    𝒲.AsphericalFunctor (Cat.Hom.ofFunctor (Functor.nerveEvalTerminal ht C) :
      (elementsFunctor B).obj (j.nerve C) ⟶ C) := fun c =>
  𝒲.aspherical_of_equivalence (Functor.nerveOverEquivalence C c ht).symm (h c)

theorem wPsh_whiskerLeft_over_iff (a : A) {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    𝒲.wPsh (Over a) (Functor.whiskerLeft (Over.forget a).op f) ↔ 𝒲.wPsh A (yoneda.obj a ◁ f) :=
  𝒲.W_iff_of_isEquivalence_of_iso
    (elementsOverRestrictEquivalence A a X).functor.toCatHom
    (elementsOverRestrictEquivalence A a Y).functor.toCatHom
    (elementsOverRestrictEquivalence A a X).isEquivalence_functor
    (elementsOverRestrictEquivalence A a Y).isEquivalence_functor _ _ (Iso.refl _)

private noncomputable def evalTerminalOver [∀ a, HasTerminal (i.obj a)] (a : A)
    (C : Cat.{u, u}) : (elementsFunctor (Over a)).obj ((Over.forget a ⋙ i).nerve C) ⟶ C :=
  Cat.Hom.ofFunctor (Functor.nerveEvalTerminal (t := fun b => ⊤_ (i.obj b.left))
    (fun b => (terminalIsTerminal : IsTerminal (⊤_ (i.obj b.left)))) C)

private theorem asphericalFunctor_evalTerminalOver [∀ a, HasTerminal (i.obj a)]
    (h : ∀ (C : Cat.{u, u}) [HasTerminal C], 𝒲.LocallyAspherical A (i.nerve C)) (a : A)
    (C : Cat.{u, u}) : 𝒲.AsphericalFunctor (evalTerminalOver i a C) :=
  𝒲.asphericalFunctor_nerveEvalTerminal _ C fun c =>
    have : HasTerminal (Cat.of (Over c)) := Over.mkIdTerminal.hasTerminal
    (𝒲.pshAspherical_over_iff a _).2 (h (Cat.of (Over c)) a)

private theorem locallyAspherical_nerve_of_forall [∀ a, HasTerminal (i.obj a)]
    (h : ∀ (C : Cat.{u, u}) [HasTerminal C], 𝒲.LocallyAspherical A (i.nerve C))
    (C : Cat.{u, u}) (hC : 𝒲.Aspherical C) : 𝒲.LocallyAspherical A (i.nerve C) := fun a => by
  rw [← 𝒲.pshAspherical_over_iff]
  exact (𝒲.aspherical_iff_of_W _
    (𝒲.W_of_asphericalFunctor (asphericalFunctor_evalTerminalOver i 𝒲 h a C))).2 hC

private def nervePoint (b : Bool) : ⊤_ (Aᵒᵖ ⥤ Type u) ⟶ i.nerve interval.{u} where
  app a := TypeCat.ofHom fun _ => (Functor.const (i.obj a.unop)).obj (show interval.{u} from ⟨b⟩)

private noncomputable def nerveInterval [∀ a, HasTerminal (i.obj a)] :
    SeparatingInterval.{u, u} A where
  interval := i.nerve interval.{u}
  pt := nervePoint i
  isPullback := Homotopical.isPullback_of_app_ne _ fun a _ _ h => by
    have := congrArg (fun F : i.obj a.unop ⥤ interval.{u} => (F.obj (⊤_ (i.obj a.unop))).down) h
    exact Bool.false_ne_true this

theorem isLocalTestFunctor_iff [∀ a, HasTerminal (i.obj a)] :
    𝒲.IsLocalTestFunctor i ↔
      ∀ (C : Cat.{u, u}) [HasTerminal C], 𝒲.LocallyAspherical A (i.nerve C) := by
  refine ⟨fun hi C _ => hi.locallyAspherical_nerve C (𝒲.terminal_aspherical C), fun h =>
    ⟨?_, fun a => 𝒲.terminal_aspherical (i.obj a), locallyAspherical_nerve_of_forall i 𝒲 h⟩⟩
  exact 𝒲.isLocalTest_of_separatingInterval A (nerveInterval i) (h interval.{u})

section Interval

variable (C : Cat.{u, u}) [HasTerminal C]

private noncomputable def contraction : Cat.of (C × interval.{u}) ⟶ C :=
  natTransHomotopy (A := C) (B := C) (F := 𝟭 C) (G := (Functor.const C).obj (⊤_ C))
    { app c := terminal.from c }

private noncomputable def nerveHomotopy (a : A) :
    i.nerve interval.{u} ⊗ (yoneda.obj a ⊗ i.nerve C) ⟶ yoneda.obj a ⊗ i.nerve C where
  app _ := TypeCat.ofHom fun p => (p.2.1, p.2.2.prod' p.1 ⋙ (contraction C).toFunctor)

private def nerveEnd (a : A) (b : Bool) :
    yoneda.obj a ⊗ i.nerve C ⟶ i.nerve interval.{u} ⊗ (yoneda.obj a ⊗ i.nerve C) where
  app x := TypeCat.ofHom fun q =>
    ((Functor.const (i.obj x.unop)).obj (show interval.{u} from ⟨b⟩), q)

private noncomputable def nerveTerminalSection (a : A) :
    yoneda.obj a ⟶ yoneda.obj a ⊗ i.nerve C where
  app x := TypeCat.ofHom fun f => (f, (Functor.const (i.obj x.unop)).obj (⊤_ C))

private theorem locallyAspherical_nerve_of_interval
    (hJ : 𝒲.LocallyAspherical A (i.nerve interval.{u})) : 𝒲.LocallyAspherical A (i.nerve C) :=
  fun a => by
  let r := CartesianMonoidalCategory.fst (yoneda.obj a) (i.nerve C)
  let s := nerveTerminalSection i C a
  have hsr : s ≫ r = 𝟙 _ := rfl
  have he : 𝒲.wPsh A (r ≫ s) :=
    𝒲.wPsh_of_homotopic_id hJ (nerveEnd i C a true) (nerveEnd i C a false) rfl rfl
      (nerveHomotopy i C a) (r ≫ s) rfl rfl
  have hs := 𝒲.wPsh_of_retraction s r hsr he
  have hr : 𝒲.wPsh A r := (𝒲.wPsh A).of_precomp s r hs (hsr ▸ (𝒲.wPsh A).id_mem _)
  rw [𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)]
  exact (𝒲.aspherical_iff_of_W _ hr).2 (𝒲.pshAspherical_yoneda A a)

end Interval

theorem isLocalTestFunctor_iff_interval [∀ a, HasTerminal (i.obj a)] :
    𝒲.IsLocalTestFunctor i ↔ 𝒲.LocallyAspherical A (i.nerve interval.{u}) :=
  ⟨fun hi => hi.locallyAspherical_nerve _ (𝒲.terminal_aspherical _), fun hJ =>
    (𝒲.isLocalTestFunctor_iff i).2 fun C _ => locallyAspherical_nerve_of_interval i 𝒲 C hJ⟩

variable {𝒲 i}

theorem IsLocalTestFunctor.isTestFunctor (hi : 𝒲.IsLocalTestFunctor i)
    (hA : 𝒲.Aspherical (Cat.of A)) : 𝒲.IsTestFunctor i :=
  { hi with isTest := (𝒲.isTest_iff_aspherical_and_isLocalTest A).2 ⟨hA, hi.isLocalTest⟩ }

theorem IsLocalTestFunctor.asphericalFunctor_evalTerminalHom [∀ a, HasTerminal (i.obj a)]
    (hi : 𝒲.IsLocalTestFunctor i) (hA : 𝒲.Aspherical (Cat.of A)) (C : Cat.{u, u}) :
    𝒲.AsphericalFunctor (evalTerminalHom i C) :=
  𝒲.asphericalFunctor_nerveEvalTerminal _ C fun c =>
    have : HasTerminal (Cat.of (Over c)) := Over.mkIdTerminal.hasTerminal
    𝒲.pshAspherical_of_locallyAspherical hA
      (hi.locallyAspherical_nerve (Cat.of (Over c)) (𝒲.terminal_aspherical _))

theorem IsLocalTestFunctor.W_iff_wPsh_nerveMap [∀ a, HasTerminal (i.obj a)]
    (hi : 𝒲.IsLocalTestFunctor i) (hA : 𝒲.Aspherical (Cat.of A)) {C D : Cat.{u, u}}
    (F : C ⟶ D) : 𝒲.W F ↔ 𝒲.wPsh A (i.nerveMap F.toFunctor) := by
  have hC := 𝒲.W_of_asphericalFunctor (hi.asphericalFunctor_evalTerminalHom hA C)
  have hD := 𝒲.W_of_asphericalFunctor (hi.asphericalFunctor_evalTerminalHom hA D)
  have hsq := elementsFunctor_map_nerveMap_comp_evalTerminalHom i F
  constructor
  · intro hF
    refine 𝒲.W.of_postcomp _ _ hD ?_
    rw [hsq]
    exact 𝒲.W.comp_mem _ _ hC hF
  · intro hN
    refine 𝒲.W.of_precomp _ _ hC ?_
    rw [← hsq]
    exact 𝒲.W.comp_mem _ _ hN hD

theorem IsLocalTestFunctor.wPsh_whiskerLeft_nerveMap [∀ a, HasTerminal (i.obj a)]
    (hi : 𝒲.IsLocalTestFunctor i) {C D : Cat.{u, u}} {F : C ⟶ D} (hF : 𝒲.W F) (a : A) :
    𝒲.wPsh A (yoneda.obj a ◁ i.nerveMap F.toFunctor) := by
  have h := (𝒲.isLocalTestFunctor_iff i).1 hi
  have hC := 𝒲.W_of_asphericalFunctor (asphericalFunctor_evalTerminalOver i 𝒲 h a C)
  have hD := 𝒲.W_of_asphericalFunctor (asphericalFunctor_evalTerminalOver i 𝒲 h a D)
  have hsq : (elementsFunctor (Over a)).map ((Over.forget a ⋙ i).nerveMap F.toFunctor) ≫
      evalTerminalOver i a D = evalTerminalOver i a C ≫ F :=
    Cat.Hom.ext (Functor.nerveEvalTerminal_comp (D := Over.forget a ⋙ i)
      (t := fun b => ⊤_ (i.obj b.left))
      (fun b => (terminalIsTerminal : IsTerminal (⊤_ (i.obj b.left)))) C F.toFunctor).symm
  rw [← 𝒲.wPsh_whiskerLeft_over_iff]
  change 𝒲.W ((elementsFunctor (Over a)).map ((Over.forget a ⋙ i).nerveMap F.toFunctor))
  refine 𝒲.W.of_postcomp _ _ hD ?_
  rw [hsq]
  exact 𝒲.W.comp_mem _ _ hC hF

private theorem locallyAspherical_nerve_interval_of_wPsh
    (h : ∀ {C D : Cat.{u, u}} (F : C ⟶ D), 𝒲.W F →
      ∀ a, 𝒲.wPsh A (yoneda.obj a ◁ i.nerveMap F.toFunctor)) :
    𝒲.LocallyAspherical A (i.nerve interval.{u}) := fun a => by
  let P : Cat.{u, u} := Cat.of (Discrete PUnit.{u + 1})
  let F : interval.{u} ⟶ P := (Functor.star _).toCatHom
  have hF := h F (𝒲.W_of_aspherical_of_hasTerminal F (𝒲.terminal_aspherical _)) a
  let r := CartesianMonoidalCategory.fst (yoneda.obj a) (i.nerve P)
  let s : yoneda.obj a ⟶ yoneda.obj a ⊗ i.nerve P :=
    { app x := TypeCat.ofHom fun f => (f, Functor.star (i.obj x.unop)) }
  have hr : 𝒲.wPsh A r := 𝒲.wPsh_of_retraction r s
    (CartesianMonoidalCategory.hom_ext _ _ rfl (by
      ext x ⟨f, G⟩
      exact Functor.punit_ext' _ _))
    ((𝒲.wPsh A).id_mem _)
  rw [𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)]
  exact (𝒲.aspherical_iff_of_W _ ((𝒲.wPsh A).comp_mem _ _ hF hr)).2 (𝒲.pshAspherical_yoneda A a)

variable (𝒲 i) in
theorem isLocalTestFunctor_iff_wPsh_whiskerLeft_nerveMap [∀ a, HasTerminal (i.obj a)] :
    𝒲.IsLocalTestFunctor i ↔ ∀ {C D : Cat.{u, u}} (F : C ⟶ D), 𝒲.W F →
      ∀ a, 𝒲.wPsh A (yoneda.obj a ◁ i.nerveMap F.toFunctor) :=
  ⟨fun hi _ _ _ hF a => hi.wPsh_whiskerLeft_nerveMap hF a, fun h =>
    (𝒲.isLocalTestFunctor_iff_interval i).2 (locallyAspherical_nerve_interval_of_wPsh h)⟩

end BasicLocalizer

end Atoms.TestCategory

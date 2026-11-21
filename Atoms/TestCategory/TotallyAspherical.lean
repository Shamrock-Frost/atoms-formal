import Atoms.TestCategory.SeparatingIntervalCriterion
import Mathlib.CategoryTheory.Localization.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

open CategoryTheory Limits MorphismProperty MonoidalCategory Opposite

namespace Atoms.TestCategory

universe u

namespace BasicLocalizer

section Cat

variable (𝒲 : BasicLocalizer.{u})

instance isMultiplicative_W : 𝒲.W.IsMultiplicative where

theorem asphericalFunctor_tensorHom {A B A' B' : Cat.{u, u}} {f : A ⟶ B} {g : A' ⟶ B'}
    (hf : 𝒲.AsphericalFunctor f) (hg : 𝒲.AsphericalFunctor g) :
    𝒲.AsphericalFunctor (f ⊗ₘ g) := by
  rintro ⟨b, b'⟩
  exact 𝒲.aspherical_of_equivalence
    (A := Cat.of (CostructuredArrow f.toFunctor b × CostructuredArrow g.toFunctor b'))
    (CostructuredArrow.prodEquivalence f.toFunctor g.toFunctor b b').symm
    (𝒲.aspherical_prod (hf b) (hg b'))

theorem asphericalFunctor_comp_iff {A B C : Cat.{u, u}} {f : A ⟶ B}
    (hf : 𝒲.AsphericalFunctor f) (g : B ⟶ C) :
    𝒲.AsphericalFunctor (f ≫ g) ↔ 𝒲.AsphericalFunctor g := by
  refine forall_congr' fun c => ?_
  have hpre : 𝒲.AsphericalFunctor
      (CostructuredArrow.pre f.toFunctor g.toFunctor c).toCatHom := fun d =>
    (𝒲.aspherical_iff_of_equivalence (B := Cat.of (CostructuredArrow f.toFunctor d.left))
      (A := Cat.of (CostructuredArrow
        (CostructuredArrow.pre f.toFunctor g.toFunctor c).toCatHom.toFunctor d))
      (CostructuredArrow.preEquivalence f.toFunctor d)).2 (hf d.left)
  exact 𝒲.aspherical_iff_of_W _ (𝒲.W_of_asphericalFunctor hpre)

instance isMonoidal_W : 𝒲.W.IsMonoidal :=
  .mk' _ fun {A B A' B'} f g hf hg => by
    have hid : ∀ (C : Cat.{u, u}) {A' B' : Cat.{u, u}} {g : A' ⟶ B'}, 𝒲.W g →
        𝒲.W (𝟙 C ⊗ₘ g) := fun C A' B' g hg =>
      𝒲.quillenA (𝟙 C ⊗ₘ g) (CategoryTheory.Prod.fst ↥C ↥B').toCatHom fun c =>
        𝒲.W.of_postcomp _ (Cat.sliceFstSnd C B' c)
          (𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_sliceFstSnd C B' c))
          (𝒲.W.comp_mem (Cat.sliceFstSnd C A' c) g
            (𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_sliceFstSnd C A' c)) hg)
    have hiso : ∀ {X Y : Cat.{u, u}} (e : X ≅ Y), 𝒲.W e.hom := fun _ =>
      MorphismProperty.isomorphisms_le_of_containsIdentities 𝒲.W _
        (MorphismProperty.isomorphisms.infer_property _)
    have hf' : 𝒲.W (f ▷ A') := by
      have e : f ▷ A' = (β_ A A').hom ≫ (A' ◁ f) ≫ (β_ B A').inv := by simp
      rw [e, ← id_tensorHom]
      exact 𝒲.W.comp_mem _ _ (hiso _)
        (𝒲.W.comp_mem _ _ (hid A' hf) (hiso (β_ B A').symm))
    rw [tensorHom_def, ← id_tensorHom]
    exact 𝒲.W.comp_mem _ _ hf' (hid B hg)

end Cat

section Slice

variable {A : Type u} [SmallCategory A]

private abbrev elementsProdComparison (X Y : Aᵒᵖ ⥤ Type u) :
    ((X ⊗ Y).Elements)ᵒᵖ ⥤ (X.Elements)ᵒᵖ × (Y.Elements)ᵒᵖ :=
  (CategoryOfElements.map (CartesianMonoidalCategory.fst X Y)).op.prod'
    (CategoryOfElements.map (CartesianMonoidalCategory.snd X Y)).op

section ProdComparison

variable (X Y : Aᵒᵖ ⥤ Type u) (p : (X.Elements)ᵒᵖ) (q : (Y.Elements)ᵒᵖ)

private def elementsProdComparisonSliceToElements :
    CostructuredArrow (elementsProdComparison X Y) (p, q) ⥤
      ((FunctorToTypes.prod (yoneda.obj (unop p.unop.1))
        (yoneda.obj (unop q.unop.1))).Elements)ᵒᵖ where
  obj α := op ⟨α.left.unop.1, (α.hom.1.unop.1.unop, α.hom.2.unop.1.unop)⟩
  map φ := Quiver.Hom.op ⟨φ.left.unop.1, Prod.ext
    (congrArg (fun k => k.1.unop.1.unop) (CostructuredArrow.w φ))
    (congrArg (fun k => k.2.unop.1.unop) (CostructuredArrow.w φ))⟩
  map_id _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)

private def elementsToElementsProdComparisonSlice :
    ((FunctorToTypes.prod (yoneda.obj (unop p.unop.1))
        (yoneda.obj (unop q.unop.1))).Elements)ᵒᵖ ⥤
      CostructuredArrow (elementsProdComparison X Y) (p, q) where
  obj e := CostructuredArrow.mk (S := elementsProdComparison X Y) (T := (p, q))
    (Y := op ((X ⊗ Y).elementsMk e.unop.1
      (X.map e.unop.2.1.op p.unop.2, Y.map e.unop.2.2.op q.unop.2)))
    (Quiver.Hom.op (CategoryOfElements.homMk _ _ e.unop.2.1.op rfl),
      Quiver.Hom.op (CategoryOfElements.homMk _ _ e.unop.2.2.op rfl))
  map {e e'} ψ := CostructuredArrow.homMk
    (Quiver.Hom.op ⟨ψ.unop.1, Prod.ext (by
      have hg : ψ.unop.1.unop ≫ e'.unop.2.1 = e.unop.2.1 := congrArg Prod.fst ψ.unop.2
      change X.map ψ.unop.1 (X.map e'.unop.2.1.op p.unop.2) = X.map e.unop.2.1.op p.unop.2
      rw [← hg, op_comp, Functor.map_comp_apply]
      rfl) (by
      have hg : ψ.unop.1.unop ≫ e'.unop.2.2 = e.unop.2.2 := congrArg Prod.snd ψ.unop.2
      change Y.map ψ.unop.1 (Y.map e'.unop.2.2.op q.unop.2) = Y.map e.unop.2.2.op q.unop.2
      rw [← hg, op_comp, Functor.map_comp_apply]
      rfl)⟩)
    (by
      have hf : ψ.unop.1.unop ≫ e'.unop.2.1 = e.unop.2.1 := congrArg Prod.fst ψ.unop.2
      have hg : ψ.unop.1.unop ≫ e'.unop.2.2 = e.unop.2.2 := congrArg Prod.snd ψ.unop.2
      refine Prod.ext ?_ ?_
      · exact Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (by
          change e'.unop.2.1.op ≫ ψ.unop.1 = e.unop.2.1.op
          rw [← hf, op_comp]
          rfl))
      · exact Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (by
          change e'.unop.2.2.op ≫ ψ.unop.1 = e.unop.2.2.op
          rw [← hg, op_comp]
          rfl)))
  map_id _ := CostructuredArrow.hom_ext _ _
    (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl))
  map_comp _ _ := CostructuredArrow.hom_ext _ _
    (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl))

private def elementsProdComparisonSliceEquivalence :
    CostructuredArrow (elementsProdComparison X Y) (p, q) ≌
      ((FunctorToTypes.prod (yoneda.obj (unop p.unop.1))
        (yoneda.obj (unop q.unop.1))).Elements)ᵒᵖ where
  functor := elementsProdComparisonSliceToElements X Y p q
  inverse := elementsToElementsProdComparisonSlice X Y p q
  unitIso := NatIso.ofComponents
    (fun α => CostructuredArrow.isoMk
      (Iso.op (CategoryOfElements.isoMk
        ((X ⊗ Y).elementsMk α.left.unop.1
          (X.map α.hom.1.unop.1 p.unop.2, Y.map α.hom.2.unop.1 q.unop.2))
        α.left.unop (Iso.refl α.left.unop.1) (by
          have h : ((X.map α.hom.1.unop.1 p.unop.2, Y.map α.hom.2.unop.1 q.unop.2) :
              (X ⊗ Y).obj α.left.unop.1) = α.left.unop.2 :=
            Prod.ext α.hom.1.unop.2 α.hom.2.unop.2
          exact (ConcreteCategory.congr_hom ((X ⊗ Y).map_id _) _).trans h)))
      (Prod.ext (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (Category.comp_id _)))
        (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (Category.comp_id _)))))
    (fun _ => CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj
      (CategoryOfElements.ext _ _ _ ((Category.id_comp _).trans (Category.comp_id _).symm))))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
    Quiver.Hom.unop_inj
      (CategoryOfElements.ext _ _ _ ((Category.id_comp _).trans (Category.comp_id _).symm)))
  functor_unitIso_comp _ :=
    Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (Category.id_comp _))

end ProdComparison

variable (c : Cat.of (A × A))

private def diagSliceToElements :
    CostructuredArrow (Functor.diag A).toCatHom.toFunctor c ⥤
      ((FunctorToTypes.prod (yoneda.obj c.1) (yoneda.obj c.2)).Elements)ᵒᵖ where
  obj α := op ⟨op α.left, (α.hom.1, α.hom.2)⟩
  map φ := Quiver.Hom.op ⟨φ.left.op, Prod.ext
    (congrArg Prod.fst (CostructuredArrow.w φ)) (congrArg Prod.snd (CostructuredArrow.w φ))⟩
  map_id _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)

private def elementsToDiagSlice :
    ((FunctorToTypes.prod (yoneda.obj c.1) (yoneda.obj c.2)).Elements)ᵒᵖ ⥤
      CostructuredArrow (Functor.diag A).toCatHom.toFunctor c where
  obj e := CostructuredArrow.mk (Y := (e.unop.1.unop : Cat.of A))
    ((e.unop.2.1, e.unop.2.2) : (e.unop.1.unop, e.unop.1.unop) ⟶ c)
  map ψ := CostructuredArrow.homMk ψ.unop.1.unop
    (Prod.ext (congrArg Prod.fst ψ.unop.2) (congrArg Prod.snd ψ.unop.2))
  map_id _ := rfl
  map_comp _ _ := rfl

private def diagSliceEquivalence :
    CostructuredArrow (Functor.diag A).toCatHom.toFunctor c ≌
      ((FunctorToTypes.prod (yoneda.obj c.1) (yoneda.obj c.2)).Elements)ᵒᵖ where
  functor := diagSliceToElements c
  inverse := elementsToDiagSlice c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
    CostructuredArrow.hom_ext _ _ ((Category.comp_id _).trans (Category.id_comp _).symm))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
    Quiver.Hom.unop_inj
      (CategoryOfElements.ext _ _ _ ((Category.id_comp _).trans (Category.comp_id _).symm)))
  functor_unitIso_comp _ :=
    Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (Category.id_comp _))

end Slice

section Psh

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

class IsTotallyAspherical : Prop where
  aspherical : 𝒲.Aspherical (Cat.of A)
  pshAspherical_prod (a b : A) : 𝒲.PshAspherical A (yoneda.obj a ⨯ yoneda.obj b)

theorem pshAspherical_prod_yoneda_tfae :
    List.TFAE
      [∀ a b : A, 𝒲.PshAspherical A (yoneda.obj a ⨯ yoneda.obj b),
        ∀ X Y : Aᵒᵖ ⥤ Type u, 𝒲.PshAspherical A X → 𝒲.PshAspherical A Y →
          𝒲.PshAspherical A (X ⨯ Y),
        ∀ X Y : Aᵒᵖ ⥤ Type u,
          𝒲.W (CartesianMonoidalCategory.prodComparison (elementsFunctor A) X Y),
        ∀ X Y : Aᵒᵖ ⥤ Type u,
          𝒲.AsphericalFunctor (CartesianMonoidalCategory.prodComparison (elementsFunctor A) X Y),
        ∀ a : A, 𝒲.LocallyAspherical A (yoneda.obj a),
        ∀ X : Aᵒᵖ ⥤ Type u, 𝒲.PshAspherical A X → 𝒲.LocallyAspherical A X,
        𝒲.AsphericalFunctor (Functor.diag A).toCatHom] := by
  tfae_have 1 → 4 := fun h X Y => by
    rintro ⟨p, q⟩
    refine 𝒲.aspherical_of_equivalence
      (A := (elementsFunctor A).obj
        (FunctorToTypes.prod (yoneda.obj (unop p.unop.1)) (yoneda.obj (unop q.unop.1))))
      (elementsProdComparisonSliceEquivalence X Y p q).symm ?_
    exact (𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)).1 (h _ _)
  tfae_have 4 → 3 := fun h X Y => 𝒲.W_of_asphericalFunctor (h X Y)
  tfae_have 3 → 2 := fun h X Y hX hY => by
    refine (𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso X Y)).2 ?_
    exact (𝒲.aspherical_iff_of_W _ (h X Y)).2 (𝒲.aspherical_prod hX hY)
  tfae_have 2 → 6 := fun h X hX a => h _ X (𝒲.pshAspherical_yoneda A a) hX
  tfae_have 6 → 5 := fun h a => h _ (𝒲.pshAspherical_yoneda A a)
  tfae_have 5 → 1 := fun h a b => h b a
  tfae_have 1 ↔ 7 := by
    refine ⟨fun h => ?_, fun h a b => ?_⟩
    · intro c
      exact (𝒲.aspherical_iff_of_equivalence
        (A := Cat.of (CostructuredArrow (Functor.diag A).toCatHom.toFunctor c))
        (B := (elementsFunctor A).obj (FunctorToTypes.prod (yoneda.obj c.1) (yoneda.obj c.2)))
        (diagSliceEquivalence c)).2
        ((𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)).1 (h c.1 c.2))
    · exact (𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)).2
        ((𝒲.aspherical_iff_of_equivalence
          (A := Cat.of (CostructuredArrow (Functor.diag A).toCatHom.toFunctor
            (show Cat.of (A × A) from (a, b))))
          (B := (elementsFunctor A).obj (FunctorToTypes.prod (yoneda.obj a) (yoneda.obj b)))
          (diagSliceEquivalence (show Cat.of (A × A) from (a, b)))).1 (h (a, b)))
  tfae_finish

private theorem pshAspherical_terminal_iff :
    𝒲.PshAspherical A (⊤_ (Aᵒᵖ ⥤ Type u)) ↔ 𝒲.Aspherical (Cat.of A) :=
  𝒲.aspherical_iff_of_W _ (𝒲.W_elementsTerminalHom A)

private theorem pshAspherical_iff_of_locallyAspherical {X : Aᵒᵖ ⥤ Type u}
    (hX : 𝒲.LocallyAspherical A X) : 𝒲.PshAspherical A X ↔ 𝒲.Aspherical (Cat.of A) :=
  (𝒲.pshAspherical_iff_of_iso A (ρ_ X)).symm.trans
    ((𝒲.aspherical_iff_of_W _
      (𝒲.wPsh_snd_of_locallyAspherical A hX (𝟙_ (Aᵒᵖ ⥤ Type u)))).trans
      ((𝒲.pshAspherical_iff_of_iso A (CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
        terminalIsTerminal)).trans (pshAspherical_terminal_iff 𝒲 A)))

theorem isTotallyAspherical_iff_of_nonempty [Nonempty A] :
    𝒲.IsTotallyAspherical A ↔ ∀ a b : A, 𝒲.PshAspherical A (yoneda.obj a ⨯ yoneda.obj b) := by
  refine ⟨fun h => h.pshAspherical_prod, fun h => ⟨?_, h⟩⟩
  obtain ⟨a⟩ := ‹Nonempty A›
  have hloc := ((𝒲.pshAspherical_prod_yoneda_tfae A).out 0 4).1 h
  exact (pshAspherical_iff_of_locallyAspherical 𝒲 A (hloc a)).1 (𝒲.pshAspherical_yoneda A a)

theorem isTotallyAspherical_iff_forall_locallyAspherical_iff :
    𝒲.IsTotallyAspherical A ↔
      ∀ X : Aᵒᵖ ⥤ Type u, 𝒲.LocallyAspherical A X ↔ 𝒲.PshAspherical A X := by
  refine ⟨fun h X => ⟨fun hX => (pshAspherical_iff_of_locallyAspherical 𝒲 A hX).2 h.aspherical,
    fun hX => ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · have h6 := ((𝒲.pshAspherical_prod_yoneda_tfae A).out 0 5).1 h.pshAspherical_prod
    exact h6 X hX
  · refine (pshAspherical_terminal_iff 𝒲 A).1 ((h _).1 fun a => ?_)
    exact (𝒲.pshAspherical_iff_of_iso A (Limits.prod.rightUnitor (yoneda.obj a))).2
      (𝒲.pshAspherical_yoneda A a)
  · exact ((𝒲.pshAspherical_prod_yoneda_tfae A).out 0 4).2
      fun a => (h _).2 (𝒲.pshAspherical_yoneda A a)

instance isTotallyAspherical_of_hasTerminal_of_hasBinaryProducts [HasTerminal A]
    [HasBinaryProducts A] : 𝒲.IsTotallyAspherical A where
  aspherical := 𝒲.terminal_aspherical (Cat.of A)
  pshAspherical_prod a b :=
    (𝒲.pshAspherical_iff_of_iso A (PreservesLimitPair.iso yoneda a b)).1
      (𝒲.pshAspherical_yoneda A (a ⨯ b))

instance isMultiplicative_wPsh : (𝒲.wPsh A).IsMultiplicative where

theorem isTotallyAspherical_iff_isMonoidal_wPsh (hA : 𝒲.Aspherical (Cat.of A)) :
    𝒲.IsTotallyAspherical A ↔ (𝒲.wPsh A).IsMonoidal := by
  refine ⟨fun h => .mk' _ fun {X X' Y Y'} f g hf hg => ?_, fun h => ⟨hA, fun a b => ?_⟩⟩
  · have hc := ((𝒲.pshAspherical_prod_yoneda_tfae A).out 0 2).1 h.pshAspherical_prod
    refine 𝒲.W.of_postcomp _ _ (hc X' Y') ?_
    rw [CartesianMonoidalCategory.prodComparison_natural]
    exact 𝒲.W.comp_mem _ _ (hc X Y) (𝒲.W.tensorHom_mem _ _ hf hg)
  · have hT : 𝒲.PshAspherical A (𝟙_ (Aᵒᵖ ⥤ Type u)) :=
      (𝒲.pshAspherical_iff_of_iso A (CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
        terminalIsTerminal)).2 ((pshAspherical_terminal_iff 𝒲 A).2 hA)
    have hto : ∀ c : A, 𝒲.wPsh A (CartesianMonoidalCategory.toUnit (yoneda.obj c)) := fun c =>
      𝒲.wPsh_of_pshAspherical A _ (𝒲.pshAspherical_yoneda A c) hT
    refine (𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)).2 ?_
    refine (𝒲.aspherical_iff_of_W _ ((𝒲.wPsh A).tensorHom_mem _ _ (hto a) (hto b))).2 ?_
    exact (𝒲.pshAspherical_iff_of_iso A (λ_ _)).2 hT

end Psh

section Functor

variable (𝒲 : BasicLocalizer.{u})

private def exchangeEquivalence (A B : Type u) [SmallCategory A] [SmallCategory B] :
    (A × A) × (B × B) ≌ (A × B) × (A × B) where
  functor := ((CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.fst _ _).prod'
      (CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.fst _ _)).prod'
    ((CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.snd _ _).prod'
      (CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.snd _ _))
  inverse := ((CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.fst _ _).prod'
      (CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.fst _ _)).prod'
    ((CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.snd _ _).prod'
      (CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.snd _ _))
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance isTotallyAspherical_prod {A B : Type u} [SmallCategory A] [SmallCategory B]
    [hA : 𝒲.IsTotallyAspherical A] [hB : 𝒲.IsTotallyAspherical B] :
    𝒲.IsTotallyAspherical (A × B) := by
  refine ⟨𝒲.aspherical_prod (A := Cat.of A) (B := Cat.of B) hA.aspherical hB.aspherical, ?_⟩
  refine ((𝒲.pshAspherical_prod_yoneda_tfae (A × B)).out 0 6).2 ?_
  have hdA := ((𝒲.pshAspherical_prod_yoneda_tfae A).out 0 6).1 hA.pshAspherical_prod
  have hdB := ((𝒲.pshAspherical_prod_yoneda_tfae B).out 0 6).1 hB.pshAspherical_prod
  have e : (Functor.diag (A × B)).toCatHom =
      ((Functor.diag A).toCatHom ⊗ₘ (Functor.diag B).toCatHom) ≫
        (exchangeEquivalence A B).functor.toCatHom := rfl
  rw [e]
  exact (𝒲.asphericalFunctor_comp_iff (𝒲.asphericalFunctor_tensorHom hdA hdB) _).2
    (𝒲.asphericalFunctor_of_adjunction (v := (exchangeEquivalence A B).inverse.toCatHom)
      (exchangeEquivalence A B).toAdjunction)

theorem isTotallyAspherical_of_asphericalFunctor {A B : Type u} [SmallCategory A]
    [SmallCategory B] [hA : 𝒲.IsTotallyAspherical A] (F : A ⥤ B)
    (hF : 𝒲.AsphericalFunctor F.toCatHom) : 𝒲.IsTotallyAspherical B := by
  refine ⟨(𝒲.aspherical_iff_of_W F.toCatHom (𝒲.W_of_asphericalFunctor hF)).1 hA.aspherical, ?_⟩
  refine ((𝒲.pshAspherical_prod_yoneda_tfae B).out 0 6).2 ?_
  have hdA := ((𝒲.pshAspherical_prod_yoneda_tfae A).out 0 6).1 hA.pshAspherical_prod
  have e : F.toCatHom ≫ (Functor.diag B).toCatHom =
      (Functor.diag A).toCatHom ≫ (F.toCatHom ⊗ₘ F.toCatHom) := rfl
  refine (𝒲.asphericalFunctor_comp_iff hF _).1 ?_
  rw [e]
  exact (𝒲.asphericalFunctor_comp_iff hdA _).2 (𝒲.asphericalFunctor_tensorHom hF hF)

end Functor

end BasicLocalizer

end Atoms.TestCategory

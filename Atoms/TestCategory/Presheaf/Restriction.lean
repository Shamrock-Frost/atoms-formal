import Atoms.TestCategory.BasicLocalizer.SmoothFunctor
import Atoms.TestCategory.Presheaf.Aspherical

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

variable {A B : Type u} [SmallCategory A] [SmallCategory B]

namespace BasicLocalizer

def elementsRestriction (u : A ⥤ B) (X : Bᵒᵖ ⥤ Type u) :
    (elementsFunctor A).obj (u.op ⋙ X) ⟶ (elementsFunctor B).obj X :=
  (Functor.Elements.precomp u.op X).op.toCatHom

@[simp]
theorem elementsRestriction_obj (u : A ⥤ B) (X : Bᵒᵖ ⥤ Type u)
    (x : (elementsFunctor A).obj (u.op ⋙ X)) :
    (elementsRestriction u X).toFunctor.obj x =
      op (X.elementsMk (op (u.obj x.unop.1.unop)) x.unop.2) := rfl

theorem isPullback_elementsRestriction (u : A ⥤ B) (X : Bᵒᵖ ⥤ Type u) :
    IsPullback (elementsRestriction u X)
      (CategoryOfElements.π (u.op ⋙ X)).leftOp.toCatHom
      (CategoryOfElements.π X).leftOp.toCatHom u.toCatHom := by
  refine Cat.isPullback_of_elementwise rfl ?_ ?_ ?_ ?_
  · rintro (⟨⟨⟨a₁⟩, x₁⟩⟩ : (u.op ⋙ X).Elementsᵒᵖ) (⟨⟨⟨a₂⟩, x₂⟩⟩ : (u.op ⋙ X).Elementsᵒᵖ) h₁ h₂
    change a₁ = a₂ at h₂
    subst h₂
    have h := Opposite.op_injective h₁
    exact congrArg (fun y => op (⟨op a₁, y⟩ : (u.op ⋙ X).Elements)) (eq_of_heq (Sigma.mk.inj h).2)
  · rintro (⟨⟨⟨b⟩, x⟩⟩ : X.Elementsᵒᵖ) (a : A) (h : b = u.obj a)
    subst h
    exact ⟨op ⟨op a, x⟩, rfl, rfl⟩
  · intro p₁ p₂ γ₁ γ₂ h₁ h₂
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact Quiver.Hom.unop_inj h₂
  · rintro (⟨⟨⟨a₁⟩, x₁⟩⟩ : (u.op ⋙ X).Elementsᵒᵖ) (⟨⟨⟨a₂⟩, x₂⟩⟩ : (u.op ⋙ X).Elementsᵒᵖ) α β e
    have e' : α.unop.val.unop = u.map β := e.trans ((Category.id_comp _).trans (Category.comp_id _))
    have hβ : α.unop.val = (u.map β).op := Quiver.Hom.unop_inj e'
    have hp : (u.op ⋙ X).map β.op x₂ = x₁ := by
      have := α.unop.2
      rw [hβ] at this
      exact this
    refine ⟨(CategoryOfElements.homMk ⟨op a₂, x₂⟩ ⟨op a₁, x₁⟩ β.op hp).op, ?_, rfl⟩
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact hβ.symm

variable (𝒲 : BasicLocalizer.{u})

private def costructuredToElements (u : A ⥤ B) (b : B) :
    CostructuredArrow u b ⥤ ((u.op ⋙ yoneda.obj b).Elements)ᵒᵖ where
  obj x := op ((u.op ⋙ yoneda.obj b).elementsMk (op x.left) x.hom)
  map {x y} g := (CategoryOfElements.homMk ((u.op ⋙ yoneda.obj b).elementsMk (op y.left) y.hom)
    ((u.op ⋙ yoneda.obj b).elementsMk (op x.left) x.hom) g.left.op (by
      change u.map g.left ≫ y.hom = x.hom
      exact CostructuredArrow.w g)).op
  map_id _ := rfl
  map_comp _ _ := rfl

private def elementsToCostructured (u : A ⥤ B) (b : B) :
    ((u.op ⋙ yoneda.obj b).Elements)ᵒᵖ ⥤ CostructuredArrow u b where
  obj x := CostructuredArrow.mk (Y := x.unop.1.unop) x.unop.2
  map {x y} f := CostructuredArrow.homMk f.unop.val.unop (by
    have := f.unop.2
    exact this)
  map_id _ := rfl
  map_comp _ _ := rfl

private def costructuredElementsIso (u : A ⥤ B) (b : B) :
    Cat.of (CostructuredArrow u b) ≅ (elementsFunctor A).obj (u.op ⋙ yoneda.obj b) where
  hom := (costructuredToElements u b).toCatHom
  inv := (elementsToCostructured u b).toCatHom
  hom_inv_id := Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)
  inv_hom_id := Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)

private theorem aspherical_costructured_iff (u : A ⥤ B) (b : B) :
    𝒲.Aspherical (Cat.of (CostructuredArrow u b)) ↔
      𝒲.PshAspherical A (u.op ⋙ yoneda.obj b) :=
  𝒲.aspherical_iff_of_equivalence (Cat.equivOfIso (costructuredElementsIso u b))

private theorem asphericalFunctor_iff_yoneda (u : A ⥤ B) :
    𝒲.AsphericalFunctor u.toCatHom ↔ ∀ b : B, 𝒲.PshAspherical A (u.op ⋙ yoneda.obj b) :=
  forall_congr' fun b => 𝒲.aspherical_costructured_iff u b

private theorem W_elementsRestriction_yoneda_iff (u : A ⥤ B) (b : B) :
    𝒲.W (elementsRestriction u (yoneda.obj b)) ↔ 𝒲.PshAspherical A (u.op ⋙ yoneda.obj b) :=
  (𝒲.aspherical_iff_W _ (𝒲.pshAspherical_yoneda B b)).symm

private theorem asphericalFunctor_elementsRestriction (u : A ⥤ B)
    (hu : 𝒲.AsphericalFunctor u.toCatHom) (X : Bᵒᵖ ⥤ Type u) :
    𝒲.AsphericalFunctor (elementsRestriction u X) :=
  𝒲.asphericalFunctor_of_isPullback_of_isDiscreteFibration
    (isPullback_elementsRestriction u X).flip (isDiscreteFibration_elements_proj X) hu

theorem asphericalFunctor_tfae (u : A ⥤ B) :
    List.TFAE
      [𝒲.AsphericalFunctor u.toCatHom,
       ∀ X : Bᵒᵖ ⥤ Type u, 𝒲.PshAspherical B X ↔ 𝒲.PshAspherical A (u.op ⋙ X),
       ∀ X : Bᵒᵖ ⥤ Type u, 𝒲.PshAspherical B X → 𝒲.PshAspherical A (u.op ⋙ X),
       ∀ b : B, 𝒲.PshAspherical A (u.op ⋙ yoneda.obj b),
       ∀ X : Bᵒᵖ ⥤ Type u, 𝒲.W (elementsRestriction u X),
       ∀ X : Bᵒᵖ ⥤ Type u, 𝒲.AsphericalFunctor (elementsRestriction u X),
       ∀ b : B, 𝒲.W (elementsRestriction u (yoneda.obj b))] := by
  tfae_have 1 → 6 := fun hu X => 𝒲.asphericalFunctor_elementsRestriction u hu X
  tfae_have 6 → 5 := fun h X => 𝒲.W_of_asphericalFunctor (h X)
  tfae_have 5 → 2 := fun h X =>
    (𝒲.aspherical_iff_of_W _ (h X)).symm
  tfae_have 2 → 3 := fun h X => (h X).1
  tfae_have 3 → 4 := fun h b => h _ (𝒲.pshAspherical_yoneda B b)
  tfae_have 4 → 1 := fun h => (𝒲.asphericalFunctor_iff_yoneda u).2 h
  tfae_have 5 → 7 := fun h b => h _
  tfae_have 7 → 4 := fun h b => (𝒲.W_elementsRestriction_yoneda_iff u b).1 (h b)
  tfae_finish

theorem wPsh_whiskerLeft_iff {u : A ⥤ B} (hu : 𝒲.AsphericalFunctor u.toCatHom)
    {X Y : Bᵒᵖ ⥤ Type u} (φ : X ⟶ Y) :
    𝒲.wPsh A (Functor.whiskerLeft u.op φ) ↔ 𝒲.wPsh B φ := by
  have hW := ((𝒲.asphericalFunctor_tfae u).out 0 4).1 hu
  have sq : (elementsFunctor A).map (Functor.whiskerLeft u.op φ) ≫ elementsRestriction u Y =
      elementsRestriction u X ≫ (elementsFunctor B).map φ := rfl
  change 𝒲.W _ ↔ 𝒲.W _
  rw [← 𝒲.W.postcomp_iff _ _ (hW Y), sq, 𝒲.W.precomp_iff _ _ (hW X)]

private theorem pshAspherical_whisker_terminal (u : A ⥤ B) (hA : 𝒲.Aspherical (Cat.of A)) :
    𝒲.PshAspherical A (u.op ⋙ ⊤_ (Bᵒᵖ ⥤ Type u)) := by
  have ht : IsTerminal (u.op ⋙ ⊤_ (Bᵒᵖ ⥤ Type u)) :=
    IsTerminal.isTerminalObj ((Functor.whiskeringLeft Aᵒᵖ Bᵒᵖ (Type u)).obj u.op) _
      terminalIsTerminal
  rw [𝒲.pshAspherical_iff_of_iso A (ht.uniqueUpToIso terminalIsTerminal)]
  exact (𝒲.aspherical_iff_of_W _ (𝒲.W_elementsTerminalHom A)).2 hA

theorem asphericalFunctor_iff_wPsh_whiskerLeft {u : A ⥤ B} (hA : 𝒲.Aspherical (Cat.of A))
    (hB : 𝒲.Aspherical (Cat.of B)) :
    𝒲.AsphericalFunctor u.toCatHom ↔
      ∀ ⦃X Y : Bᵒᵖ ⥤ Type u⦄ (φ : X ⟶ Y), 𝒲.wPsh B φ → 𝒲.wPsh A (Functor.whiskerLeft u.op φ) :=
  ⟨fun hu _ _ φ h => (𝒲.wPsh_whiskerLeft_iff hu φ).2 h, fun h => by
    refine ((𝒲.asphericalFunctor_tfae u).out 0 2).2 fun X hX => ?_
    have h1 := h _ ((𝒲.pshAspherical_iff_wPsh_terminal_from B hB X).1 hX)
    exact (𝒲.aspherical_iff_of_W _ h1).2 (𝒲.pshAspherical_whisker_terminal u hA)⟩

end BasicLocalizer

end Atoms.TestCategory

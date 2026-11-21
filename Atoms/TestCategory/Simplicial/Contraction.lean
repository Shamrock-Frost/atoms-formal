import Atoms.TestCategory.Simplicial.SimplexTest

open CategoryTheory Limits Opposite
open Atoms.Homotopical Simplicial MorphismProperty MonoidalCategory

universe u

namespace Atoms.TestCategory

private def nerveProdMap (C D : Type u) [SmallCategory C] [SmallCategory D] :
    CategoryTheory.nerve C ⊗ CategoryTheory.nerve D ⟶
      CategoryTheory.nerve (C × D) where
  app _ := ↾fun p => p.1.prod' p.2
  naturality _ _ _ := by
    ext p
    rfl

private def finTwoToInterval : ULift.{u} (Fin 2) ⥤ ULift.{u} Bool where
  obj i := ULift.up (i.down = 1)
  map {i j} f := homOfLE (by
    have h : i.down ≤ j.down := f.down.down
    by_cases hi : i.down = 1
    · have hj : j.down = 1 := by omega
      simp [hi, hj]
    · simp [hi])
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private def terminalContractionNatTrans {D : Type u} [SmallCategory D] {t : D}
    (ht : IsTerminal t) : 𝟭 D ⟶ (Functor.const D).obj t where
  app d := ht.from d
  naturality _ _ _ := ht.hom_ext _ _

def terminalContractionFunctor {D : Type u} [SmallCategory D] {t : D}
    (ht : IsTerminal t) : ULift (Fin 2) × D ⥤ D :=
  (CategoryTheory.Prod.swap (ULift (Fin 2)) D) ⋙
    ((CategoryTheory.Prod.fst D (ULift (Fin 2))).prod'
      (CategoryTheory.Prod.snd D (ULift (Fin 2)) ⋙ finTwoToInterval)) ⋙
        (natTransHomotopy (A := Cat.of D) (B := Cat.of D)
          (terminalContractionNatTrans ht)).toFunctor

def terminalNerveHomotopy {D : Type u} [SmallCategory D] {t : D}
    (ht : IsTerminal t) : Δ[1] ⊗ CategoryTheory.nerve D ⟶
      CategoryTheory.nerve D :=
  ((SSet.stdSimplex.isoNerve 1).hom ⊗ₘ 𝟙 _) ≫
    nerveProdMap (ULift (Fin 2)) D ≫
      CategoryTheory.nerveMap (terminalContractionFunctor ht)

structure SimplicialContraction (T : SSet.{u}) where
  pt : 𝟙_ SSet.{u} ⟶ T
  homotopy : Δ[1] ⊗ T ⟶ T
  homotopy_zero : CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.toUnit T ≫
        SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)) (𝟙 T) ≫ homotopy = 𝟙 T
  homotopy_one : CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.toUnit T ≫
        SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) (𝟙 T) ≫ homotopy =
      CartesianMonoidalCategory.toUnit T ≫ pt

def SimplicialContraction.ofIsTerminal {D : Type u} [SmallCategory D] {t : D}
    (ht : IsTerminal t) : SimplicialContraction (CategoryTheory.nerve D) where
  pt := SSet.const (ComposableArrows.mk₀ t)
  homotopy := terminalNerveHomotopy ht
  homotopy_zero := by ext n F; rfl
  homotopy_one := by ext n F; rfl

def SimplicialContraction.ofIso {T T' : SSet.{u}} (e : T ≅ T')
    (c : SimplicialContraction T) : SimplicialContraction T' where
  pt := c.pt ≫ e.hom
  homotopy := (𝟙 Δ[1] ⊗ₘ e.inv) ≫ c.homotopy ≫ e.hom
  homotopy_zero := by
    have hs : CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.toUnit T' ≫
            SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)) (𝟙 T') ≫
          (𝟙 Δ[1] ⊗ₘ e.inv) =
        e.inv ≫ CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.toUnit T ≫
              SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)) (𝟙 T) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
          CartesianMonoidalCategory.tensorHom_fst, Category.comp_id]
        have hu : CartesianMonoidalCategory.toUnit T' =
            e.inv ≫ CartesianMonoidalCategory.toUnit T :=
          CartesianMonoidalCategory.toUnit_unique _ _
        rw [hu]
        cat_disch
      · cat_disch
    calc
      _ = (e.inv ≫ CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.toUnit T ≫
              SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)) (𝟙 T)) ≫
            c.homotopy ≫ e.hom := by rw [← Category.assoc, hs]
      _ = e.inv ≫ (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.toUnit T ≫
              SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)) (𝟙 T) ≫
            c.homotopy) ≫ e.hom := by cat_disch
      _ = e.inv ≫ 𝟙 T ≫ e.hom :=
        congrArg (fun q => e.inv ≫ q ≫ e.hom) c.homotopy_zero
      _ = e.inv ≫ e.hom := by cat_disch
      _ = 𝟙 T' := e.inv_hom_id
  homotopy_one := by
    have hs : CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.toUnit T' ≫
            SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) (𝟙 T') ≫
          (𝟙 Δ[1] ⊗ₘ e.inv) =
        e.inv ≫ CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.toUnit T ≫
              SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) (𝟙 T) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
          CartesianMonoidalCategory.tensorHom_fst, Category.comp_id]
        have hu : CartesianMonoidalCategory.toUnit T' =
            e.inv ≫ CartesianMonoidalCategory.toUnit T :=
          CartesianMonoidalCategory.toUnit_unique _ _
        rw [hu]
        cat_disch
      · cat_disch
    calc
      _ = (e.inv ≫ CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.toUnit T ≫
              SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) (𝟙 T)) ≫
            c.homotopy ≫ e.hom := by rw [← Category.assoc, hs]
      _ = e.inv ≫ (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.toUnit T ≫
              SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) (𝟙 T) ≫
            c.homotopy) ≫ e.hom := by cat_disch
      _ = e.inv ≫ (CartesianMonoidalCategory.toUnit T ≫ c.pt) ≫ e.hom :=
        congrArg (fun q => e.inv ≫ q ≫ e.hom) c.homotopy_one
      _ = CartesianMonoidalCategory.toUnit T' ≫ (c.pt ≫ e.hom) := by
        have hu : e.inv ≫ CartesianMonoidalCategory.toUnit T =
            CartesianMonoidalCategory.toUnit T' :=
          CartesianMonoidalCategory.toUnit_unique _ _
        calc
          _ = (e.inv ≫ CartesianMonoidalCategory.toUnit T) ≫ (c.pt ≫ e.hom) :=
            by cat_disch
          _ = _ := congrArg (fun q => q ≫ (c.pt ≫ e.hom)) hu

def stdSimplexContraction (n : ℕ) : SimplicialContraction Δ[n] := by
  let ht : IsTerminal (ULift.up (Fin.last n) : ULift (Fin (n + 1))) :=
    IsTerminal.ofUniqueHom
      (fun x => homOfLE (show x.down ≤ Fin.last n from Fin.le_last x.down))
      (fun _ _ => rfl)
  exact SimplicialContraction.ofIso (SSet.stdSimplex.isoNerve n).symm
    (SimplicialContraction.ofIsTerminal ht)

noncomputable def overNerveContraction {A : Type u} [SmallCategory A] (a : A) :
    SimplicialContraction (CategoryTheory.nerve (Over a)) :=
  SimplicialContraction.ofIsTerminal (Over.mkIdTerminal (X := a))

namespace BasicLocalizer

theorem pshAspherical_sSetAsSmall_of_contraction (𝒲 : BasicLocalizer.{u}) {T : SSet.{u}}
    (c : SimplicialContraction T) :
    𝒲.PshAspherical (AsSmall.{u} SimplexCategory) (SSet.asSmall.obj T) := by
  let Q := SSet.asSmall.obj T
  let J := SSet.asSmall.obj Δ[1]
  let sec : Fin 2 → (Q ⟶ J ⊗ Q) := fun ε => SSet.asSmall.map
    (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.toUnit T ≫ SSet.const (SSet.stdSimplex.obj₀Equiv.symm ε)) (𝟙 T))
  have hsnd : ∀ ε, sec ε ≫ CartesianMonoidalCategory.snd J Q = 𝟙 Q := fun ε =>
    (SSet.asSmall.map_comp _ (CartesianMonoidalCategory.snd Δ[1] T)).symm.trans
      ((congrArg SSet.asSmall.map (CartesianMonoidalCategory.lift_snd _ _)).trans
        (SSet.asSmall.map_id T))
  let r : Q ⟶ SSet.asSmall.obj (𝟙_ SSet.{u}) :=
    SSet.asSmall.map (CartesianMonoidalCategory.toUnit T)
  let s : SSet.asSmall.obj (𝟙_ SSet.{u}) ⟶ Q := SSet.asSmall.map c.pt
  have he : sec 1 ≫ SSet.asSmall.map c.homotopy = r ≫ s :=
    (SSet.asSmall.map_comp _ _).symm.trans
      ((congrArg SSet.asSmall.map c.homotopy_one).trans (SSet.asSmall.map_comp _ _))
  have h1 : sec 0 ≫ SSet.asSmall.map c.homotopy = 𝟙 Q :=
    (SSet.asSmall.map_comp _ _).symm.trans
      ((congrArg SSet.asSmall.map c.homotopy_zero).trans (SSet.asSmall.map_id T))
  have hw : 𝒲.wPsh _ (r ≫ s) :=
    𝒲.wPsh_of_homotopic_id 𝒲.locallyAspherical_asSmall_stdSimplex_one (sec 1) (sec 0)
      (hsnd 1) (hsnd 0) (SSet.asSmall.map c.homotopy) (r ≫ s) he h1
  have hsr : s ≫ r = 𝟙 _ :=
    (SSet.asSmall.map_comp _ _).symm.trans
      ((congrArg SSet.asSmall.map (CartesianMonoidalCategory.toUnit_unique _ _)).trans
        (SSet.asSmall.map_id _))
  have hs : 𝒲.wPsh _ s := 𝒲.wPsh_of_retraction s r hsr hw
  have hr : 𝒲.wPsh _ r := (𝒲.wPsh _).of_precomp s r hs (hsr ▸ (𝒲.wPsh _).id_mem _)
  have ht : 𝒲.wPsh _ (terminal.from (SSet.asSmall.{u}.obj (𝟙_ SSet.{u}))) :=
    isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (isIso_of_isTerminal
      (CartesianMonoidalCategory.isTerminalTensorUnit.isTerminalObj SSet.asSmall.{u} _)
      terminalIsTerminal _)
  rw [𝒲.pshAspherical_iff_wPsh_terminal_from _ 𝒲.aspherical_asSmallSimplexCategory,
    show terminal.from Q = r ≫ terminal.from _ from terminal.hom_ext _ _]
  exact (𝒲.wPsh _).comp_mem _ _ hr ht

end BasicLocalizer

end Atoms.TestCategory

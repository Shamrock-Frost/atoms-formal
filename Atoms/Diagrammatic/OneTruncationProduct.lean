import Atoms.Diagrammatic.OneTruncation
import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal

open CategoryTheory Limits Simplicial Opposite MonoidalCategory CartesianMonoidalCategory
open Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

open scoped SimplicialSeedQuotient

namespace SimplicialSeedQuotient

open SSet.Truncated in
private theorem mapHomotopyCategory_comp {A B C : SSet.Truncated.{u} 2} (f : A ⟶ B) (g : B ⟶ C) :
    mapHomotopyCategory (f ≫ g) = mapHomotopyCategory f ⋙ mapHomotopyCategory g :=
  congrArg Cat.Hom.toFunctor (hoFunctor₂.map_comp f g)

open SSet.Truncated in
private theorem mapHomotopyCategory_id (A : SSet.Truncated.{u} 2) :
    mapHomotopyCategory (𝟙 A) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor (hoFunctor₂.map_id A)

private theorem hmap_comp {Z : DiagSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hmap[f ≫ g] = hmap[f] ⋙ hmap[g] := by
  rw [Functor.map_comp, Functor.map_comp, mapHomotopyCategory_comp]

private theorem hmap_id (X : DiagSet.{u}) : hmap[𝟙 X] = 𝟭 _ := by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, mapHomotopyCategory_id]

private noncomputable def truncProdIso (X Y : DiagSet.{u}) : tr₂[X ⨯ Y] ≅ tr₂[X] ⊗ tr₂[Y] :=
  (DiagSet.toSSet ⋙ SSet.truncation 2).mapIso
    ((prodIsProd X Y).conePointUniqueUpToIso (tensorProductIsBinaryProduct X Y))

private noncomputable def hFunctor (X Y : DiagSet.{u}) :
    SSet.Truncated.HomotopyCategory tr₂[X ⨯ Y] ⥤
      SSet.Truncated.HomotopyCategory tr₂[X] × SSet.Truncated.HomotopyCategory tr₂[Y] :=
  hmap[prod.fst].prod' hmap[prod.snd]

open SSet.Truncated.HomotopyCategory in
private noncomputable def hInverse (X Y : DiagSet.{u}) :
    SSet.Truncated.HomotopyCategory tr₂[X] × SSet.Truncated.HomotopyCategory tr₂[Y] ⥤
      SSet.Truncated.HomotopyCategory tr₂[X ⨯ Y] :=
  BinaryProduct.inverse _ _ ⋙ SSet.Truncated.mapHomotopyCategory (truncProdIso X Y).inv

open SSet.Truncated.HomotopyCategory in
private theorem hFunctor_eq : hFunctor X Y =
    SSet.Truncated.mapHomotopyCategory (truncProdIso X Y).hom ⋙ BinaryProduct.functor _ _ := by
  change _ = (SSet.Truncated.mapHomotopyCategory (truncProdIso X Y).hom ⋙
      SSet.Truncated.mapHomotopyCategory (fst _ _)).prod'
    (SSet.Truncated.mapHomotopyCategory (truncProdIso X Y).hom ⋙
      SSet.Truncated.mapHomotopyCategory (snd _ _))
  rw [← mapHomotopyCategory_comp, ← mapHomotopyCategory_comp]
  congr 2

open SSet.Truncated.HomotopyCategory in
private theorem hFunctor_comp_hInverse : hFunctor X Y ⋙ hInverse X Y = 𝟭 _ := by
  rw [hFunctor_eq]
  change SSet.Truncated.mapHomotopyCategory (truncProdIso X Y).hom ⋙
    (BinaryProduct.functor _ _ ⋙ BinaryProduct.inverse _ _) ⋙
      SSet.Truncated.mapHomotopyCategory (truncProdIso X Y).inv = _
  rw [BinaryProduct.functor_comp_inverse, Functor.id_comp, ← mapHomotopyCategory_comp,
    Iso.hom_inv_id, mapHomotopyCategory_id]

open SSet.Truncated.HomotopyCategory in
private theorem hInverse_comp_hFunctor : hInverse X Y ⋙ hFunctor X Y = 𝟭 _ := by
  rw [hFunctor_eq]
  change BinaryProduct.inverse _ _ ⋙ (SSet.Truncated.mapHomotopyCategory (truncProdIso X Y).inv ⋙
    SSet.Truncated.mapHomotopyCategory (truncProdIso X Y).hom) ⋙ BinaryProduct.functor _ _ = _
  rw [← mapHomotopyCategory_comp, Iso.inv_hom_id, mapHomotopyCategory_id, Functor.id_comp,
    BinaryProduct.inverse_comp_functor]

private instance : IsIso (toAtomPoint (atomSimplex 0)) :=
  isIso_toAtomPoint_of_dimension_eq_zero (dimension_atomSimplex 0)

private instance (U : Atom) : Subsingleton (U ⟶ atomSimplex 0) :=
  ⟨fun _ _ => (cancel_mono (toAtomPoint (atomSimplex 0))).1 (Subsingleton.elim _ _)⟩

private noncomputable def const (W : DiagSet.{u}) {Z : DiagSet.{u}}
    (z : (DiagSet.toSSet.obj Z) _⦋0⦌) : W ⟶ Z :=
  isTerminalBallAtomPoint.from W ≫ uliftYoneda.map (inv (toAtomPoint (atomSimplex 0))) ≫
    uliftYonedaEquiv.symm z

private theorem const_app (W : DiagSet.{u}) {Z : DiagSet.{u}} (z : (DiagSet.toSSet.obj Z) _⦋0⦌)
    {U : Atom} (g : U ⟶ atomSimplex 0) (w : W.obj (op U)) :
    (const W z).app (op U) w = Z.map g.op z := by
  change Z.map (toAtomPoint U ≫ inv (toAtomPoint (atomSimplex 0))).op z = _
  rw [Subsingleton.elim (toAtomPoint U ≫ inv (toAtomPoint (atomSimplex 0))) g]

private theorem hmap_const (W : DiagSet.{u}) {Z : DiagSet.{u}} (z : (DiagSet.toSSet.obj Z) _⦋0⦌) :
    hmap[const W z] = (Functor.const _).obj (SSet.Truncated.HomotopyCategory.mk z) := by
  refine SSet.Truncated.HomotopyCategory.functor_ext_of_arrowMk fun x y e => ?_
  refine (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ (SSet.Edge.id z).toTruncated
    ?_).trans (congrArg Arrow.mk (SSet.Truncated.HomotopyCategory.homMk_id _))
  exact const_app W z (simplexFunctor.map (SimplexCategory.σ 0)) _

private noncomputable def hInverseQ (X Y : DiagSet.{u}) :
    SSet.Truncated.HomotopyCategory tr₂[X] × SSet.Truncated.HomotopyCategory tr₂[Y] ⥤
      SimplicialSeedQuotient (X ⨯ Y) :=
  hInverse X Y ⋙ quotientFunctor (X ⨯ Y)

private theorem hmap_lift_eq {W : DiagSet.{u}} (f : W ⟶ X) (g : W ⟶ Y) :
    hmap[prod.lift f g] = hmap[f].prod' hmap[g] ⋙ hInverse X Y := by
  have h : hmap[prod.lift f g] ⋙ hFunctor X Y = hmap[f].prod' hmap[g] := by
    change (hmap[prod.lift f g] ⋙ hmap[prod.fst]).prod' (hmap[prod.lift f g] ⋙ hmap[prod.snd]) = _
    rw [← hmap_comp, ← hmap_comp, prod.lift_fst, prod.lift_snd]
  rw [← h, Functor.assoc, hFunctor_comp_hInverse, Functor.comp_id]

private theorem hInverseQ_map_left (y : SSet.Truncated.HomotopyCategory tr₂[Y])
    {a b : SSet.Truncated.HomotopyCategory tr₂[X]} (φ ψ : a ⟶ b) (h : Rel X φ ψ) :
    (hInverseQ X Y).map (Prod.mkHom φ (𝟙 y)) = (hInverseQ X Y).map (Prod.mkHom ψ (𝟙 y)) := by
  obtain ⟨y, rfl⟩ : ∃ y' : (DiagSet.toSSet.obj Y) _⦋0⦌,
      SSet.Truncated.HomotopyCategory.mk y' = y :=
    SSet.Truncated.HomotopyCategory.mk_surjective y
  have e : Prod.sectL _ (SSet.Truncated.HomotopyCategory.mk y) ⋙ hInverseQ X Y =
      quotientFunctor X ⋙ map (prod.lift (𝟙 X) (const X y)) := by
    rw [quotientFunctor_comp_map, hmap_lift_eq, hmap_id, hmap_const]
    rfl
  change (Prod.sectL _ _ ⋙ hInverseQ X Y).map φ = (Prod.sectL _ _ ⋙ hInverseQ X Y).map ψ
  rw [Functor.congr_hom e φ, Functor.congr_hom e ψ]
  exact congrArg (_ ≫ · ≫ _) (congrArg (map _).map
    (CategoryTheory.Quotient.sound _ h))

private theorem hInverseQ_map_right (x : SSet.Truncated.HomotopyCategory tr₂[X])
    {a b : SSet.Truncated.HomotopyCategory tr₂[Y]} (φ ψ : a ⟶ b) (h : Rel Y φ ψ) :
    (hInverseQ X Y).map (Prod.mkHom (𝟙 x) φ) = (hInverseQ X Y).map (Prod.mkHom (𝟙 x) ψ) := by
  obtain ⟨x, rfl⟩ : ∃ x' : (DiagSet.toSSet.obj X) _⦋0⦌,
      SSet.Truncated.HomotopyCategory.mk x' = x :=
    SSet.Truncated.HomotopyCategory.mk_surjective x
  have e : Prod.sectR (SSet.Truncated.HomotopyCategory.mk x) _ ⋙ hInverseQ X Y =
      quotientFunctor Y ⋙ map (prod.lift (const Y x) (𝟙 Y)) := by
    rw [quotientFunctor_comp_map, hmap_lift_eq, hmap_id, hmap_const]
    rfl
  change (Prod.sectR _ _ ⋙ hInverseQ X Y).map φ = (Prod.sectR _ _ ⋙ hInverseQ X Y).map ψ
  rw [Functor.congr_hom e φ, Functor.congr_hom e ψ]
  exact congrArg (_ ≫ · ≫ _) (congrArg (map _).map
    (CategoryTheory.Quotient.sound _ h))

section Lift₂

variable {D : Type*} [Category* D]
  (G : SSet.Truncated.HomotopyCategory tr₂[X] × SSet.Truncated.HomotopyCategory tr₂[Y] ⥤ D)
  (hX : ∀ (y : SSet.Truncated.HomotopyCategory tr₂[Y])
    (a b : SSet.Truncated.HomotopyCategory tr₂[X])
    (φ ψ : a ⟶ b), Rel X φ ψ → G.map (Prod.mkHom φ (𝟙 y)) = G.map (Prod.mkHom ψ (𝟙 y)))
  (hY : ∀ (x : SSet.Truncated.HomotopyCategory tr₂[X])
    (a b : SSet.Truncated.HomotopyCategory tr₂[Y])
    (φ ψ : a ⟶ b), Rel Y φ ψ → G.map (Prod.mkHom (𝟙 x) φ) = G.map (Prod.mkHom (𝟙 x) ψ))

private def liftRight : SSet.Truncated.HomotopyCategory tr₂[X] ⥤ SimplicialSeedQuotient Y ⥤ D where
  obj a := lift ((Functor.curry.obj G).obj a) (hY a)
  map f := CategoryTheory.Quotient.natTransLift _ ((Functor.curry.obj G).map f)
  map_id a := by
    ext ⟨b⟩
    exact G.map_id _
  map_comp f g := by
    ext ⟨b⟩
    refine (congrArg G.map ?_).trans (G.map_comp _ _)
    exact Prod.ext rfl (Category.comp_id _).symm

private def liftProd : SimplicialSeedQuotient X × SimplicialSeedQuotient Y ⥤ D :=
  Functor.uncurry.obj (lift (liftRight G hY) fun _ _ φ ψ h => by
    ext ⟨b⟩
    exact hX b _ _ φ ψ h)

private theorem prod_comp_liftProd :
    (quotientFunctor X).prod (quotientFunctor Y) ⋙ liftProd G hX hY = G :=
  Functor.ext_of_iso (NatIso.ofComponents (fun _ => Iso.refl _) fun _ =>
    (Category.comp_id _).trans (((G.map_comp _ _).symm.trans (congrArg G.map
      (Prod.ext (Category.comp_id _) (Category.id_comp _)))).trans (Category.id_comp _).symm))
    (fun _ => rfl) fun _ => rfl

end Lift₂

private theorem prod_functor_ext {D : Type*} [Category* D]
    {F₁ F₂ : SimplicialSeedQuotient X × SimplicialSeedQuotient Y ⥤ D}
    (h : (quotientFunctor X).prod (quotientFunctor Y) ⋙ F₁ =
      (quotientFunctor X).prod (quotientFunctor Y) ⋙ F₂) : F₁ = F₂ := by
  refine CategoryTheory.Functor.ext (fun ⟨⟨a⟩, ⟨b⟩⟩ => Functor.congr_obj h (a, b)) ?_
  rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨a'⟩, ⟨b'⟩⟩ ⟨f, g⟩
  induction f using Quot.inductionOn
  induction g using Quot.inductionOn
  exact Functor.congr_hom h (Prod.mkHom _ _)

private noncomputable def prodInverse (X Y : DiagSet.{u}) :
    SimplicialSeedQuotient X × SimplicialSeedQuotient Y ⥤ SimplicialSeedQuotient (X ⨯ Y) :=
  liftProd (hInverseQ X Y) (fun y _ _ => hInverseQ_map_left y) fun x _ _ => hInverseQ_map_right x

private noncomputable def prodFunctor (X Y : DiagSet.{u}) :
    SimplicialSeedQuotient (X ⨯ Y) ⥤ SimplicialSeedQuotient X × SimplicialSeedQuotient Y :=
  (map (prod.fst : X ⨯ Y ⟶ X)).prod' (map (prod.snd : X ⨯ Y ⟶ Y))

private theorem quotientFunctor_comp_prodFunctor :
    quotientFunctor (X ⨯ Y) ⋙ prodFunctor X Y =
      hFunctor X Y ⋙ (quotientFunctor X).prod (quotientFunctor Y) := by
  change (quotientFunctor (X ⨯ Y) ⋙ map prod.fst).prod'
    (quotientFunctor (X ⨯ Y) ⋙ map prod.snd) = _
  rw [quotientFunctor_comp_map, quotientFunctor_comp_map]
  rfl

private theorem prodFunctor_comp_prodInverse : prodFunctor X Y ⋙ prodInverse X Y = 𝟭 _ := by
  refine CategoryTheory.Quotient.lift_unique' _ _ _ ?_
  change (quotientFunctor (X ⨯ Y) ⋙ prodFunctor X Y) ⋙ prodInverse X Y = quotientFunctor _
  rw [quotientFunctor_comp_prodFunctor, Functor.assoc, prodInverse, prod_comp_liftProd, hInverseQ,
    ← Functor.assoc, hFunctor_comp_hInverse]
  rfl

private theorem prodInverse_comp_prodFunctor : prodInverse X Y ⋙ prodFunctor X Y = 𝟭 _ := by
  refine prod_functor_ext ?_
  rw [← Functor.assoc, prodInverse, prod_comp_liftProd, hInverseQ, Functor.assoc,
    quotientFunctor_comp_prodFunctor, ← Functor.assoc, hInverse_comp_hFunctor]
  rfl

end SimplicialSeedQuotient

namespace OneTruncation

open SimplicialSeedQuotient (ofOneTruncation toOneTruncation)

private noncomputable def prodFunctor (X Y : DiagSet.{u}) :
    OneTruncation (X ⨯ Y) ⥤ OneTruncation X × OneTruncation Y :=
  (oneTruncation.map (prod.fst : X ⨯ Y ⟶ X)).toFunctor.prod'
    (oneTruncation.map (prod.snd : X ⨯ Y ⟶ Y)).toFunctor

private noncomputable def prodInverse (X Y : DiagSet.{u}) :
    OneTruncation X × OneTruncation Y ⥤ OneTruncation (X ⨯ Y) :=
  (ofOneTruncation X).prod (ofOneTruncation Y) ⋙ SimplicialSeedQuotient.prodInverse X Y ⋙
    toOneTruncation (X ⨯ Y)

private theorem prodFunctor_comp_ofOneTruncation :
    prodFunctor X Y ⋙ (ofOneTruncation X).prod (ofOneTruncation Y) =
      ofOneTruncation (X ⨯ Y) ⋙ SimplicialSeedQuotient.prodFunctor X Y := by
  change ((oneTruncation.map prod.fst).toFunctor ⋙ ofOneTruncation X).prod'
      ((oneTruncation.map prod.snd).toFunctor ⋙ ofOneTruncation Y) =
    (ofOneTruncation (X ⨯ Y) ⋙ SimplicialSeedQuotient.map prod.fst).prod'
      (ofOneTruncation (X ⨯ Y) ⋙ SimplicialSeedQuotient.map prod.snd)
  rw [SimplicialSeedQuotient.ofOneTruncation_naturality,
    SimplicialSeedQuotient.ofOneTruncation_naturality]
  rfl

private theorem toOneTruncation_comp_prodFunctor :
    toOneTruncation (X ⨯ Y) ⋙ prodFunctor X Y =
      SimplicialSeedQuotient.prodFunctor X Y ⋙ (toOneTruncation X).prod (toOneTruncation Y) := by
  change (toOneTruncation (X ⨯ Y) ⋙ (oneTruncation.map prod.fst).toFunctor).prod'
      (toOneTruncation (X ⨯ Y) ⋙ (oneTruncation.map prod.snd).toFunctor) =
    (SimplicialSeedQuotient.map prod.fst ⋙ toOneTruncation X).prod'
      (SimplicialSeedQuotient.map prod.snd ⋙ toOneTruncation Y)
  rw [← SimplicialSeedQuotient.toOneTruncation_naturality,
    ← SimplicialSeedQuotient.toOneTruncation_naturality]
  rfl

private theorem prodFunctor_comp_prodInverse : prodFunctor X Y ⋙ prodInverse X Y = 𝟭 _ := by
  change (prodFunctor X Y ⋙ (ofOneTruncation X).prod (ofOneTruncation Y)) ⋙
    SimplicialSeedQuotient.prodInverse X Y ⋙ toOneTruncation (X ⨯ Y) = _
  rw [prodFunctor_comp_ofOneTruncation, Functor.assoc,
    ← Functor.assoc (SimplicialSeedQuotient.prodFunctor X Y),
    SimplicialSeedQuotient.prodFunctor_comp_prodInverse, Functor.id_comp,
    SimplicialSeedQuotient.ofOneTruncation_comp_toOneTruncation]

private theorem prodInverse_comp_prodFunctor : prodInverse X Y ⋙ prodFunctor X Y = 𝟭 _ := by
  change ((ofOneTruncation X).prod (ofOneTruncation Y) ⋙ SimplicialSeedQuotient.prodInverse X Y) ⋙
    (toOneTruncation (X ⨯ Y) ⋙ prodFunctor X Y) = _
  rw [toOneTruncation_comp_prodFunctor, ← Functor.assoc,
    Functor.assoc ((ofOneTruncation X).prod (ofOneTruncation Y)),
    SimplicialSeedQuotient.prodInverse_comp_prodFunctor, Functor.comp_id]
  exact congrArg₂ Functor.prod (SimplicialSeedQuotient.ofOneTruncation_comp_toOneTruncation X)
    (SimplicialSeedQuotient.ofOneTruncation_comp_toOneTruncation Y)

noncomputable def prodEquivalence (X Y : DiagSet.{u}) :
    OneTruncation (X ⨯ Y) ≌ OneTruncation X × OneTruncation Y :=
  CategoryTheory.Equivalence.mk (prodFunctor X Y) (prodInverse X Y)
    (eqToIso prodFunctor_comp_prodInverse.symm) (eqToIso prodInverse_comp_prodFunctor)

theorem prodEquivalence_functor (X Y : DiagSet.{u}) :
    (OneTruncation.prodEquivalence X Y).functor =
      (oneTruncation.map (Limits.prod.fst : X ⨯ Y ⟶ X)).toFunctor.prod'
        (oneTruncation.map (Limits.prod.snd : X ⨯ Y ⟶ Y)).toFunctor :=
  rfl

theorem prodEquivalence_functor_comp_inverse (X Y : DiagSet.{u}) :
    (OneTruncation.prodEquivalence X Y).functor ⋙ (OneTruncation.prodEquivalence X Y).inverse =
      𝟭 _ :=
  prodFunctor_comp_prodInverse

theorem prodEquivalence_inverse_comp_functor (X Y : DiagSet.{u}) :
    (OneTruncation.prodEquivalence X Y).inverse ⋙ (OneTruncation.prodEquivalence X Y).functor =
      𝟭 _ :=
  prodInverse_comp_prodFunctor

private theorem oneTruncation_map_comp_toFunctor {Z : DiagSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (oneTruncation.map f).toFunctor ⋙ (oneTruncation.map g).toFunctor =
      (oneTruncation.map (f ≫ g)).toFunctor :=
  (congrArg Cat.Hom.toFunctor (oneTruncation.map_comp f g)).symm

theorem prodEquivalence_functor_naturality {X' Y' : DiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (oneTruncation.map (prod.map f g)).toFunctor ⋙ (prodEquivalence X' Y').functor =
      (prodEquivalence X Y).functor ⋙
        (oneTruncation.map f).toFunctor.prod (oneTruncation.map g).toFunctor := by
  change ((oneTruncation.map (prod.map f g)).toFunctor ⋙
      (oneTruncation.map prod.fst).toFunctor).prod'
    ((oneTruncation.map (prod.map f g)).toFunctor ⋙ (oneTruncation.map prod.snd).toFunctor) =
    ((oneTruncation.map prod.fst).toFunctor ⋙ (oneTruncation.map f).toFunctor).prod'
      ((oneTruncation.map prod.snd).toFunctor ⋙ (oneTruncation.map g).toFunctor)
  rw [oneTruncation_map_comp_toFunctor, oneTruncation_map_comp_toFunctor,
    oneTruncation_map_comp_toFunctor, oneTruncation_map_comp_toFunctor, prod.map_fst,
    prod.map_snd]

theorem prodEquivalence_inverse_naturality {X' Y' : DiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (oneTruncation.map f).toFunctor.prod (oneTruncation.map g).toFunctor ⋙
        (prodEquivalence X' Y').inverse =
      (prodEquivalence X Y).inverse ⋙ (oneTruncation.map (prod.map f g)).toFunctor :=
  (congrArg (· ⋙ (oneTruncation.map f).toFunctor.prod (oneTruncation.map g).toFunctor ⋙
      (prodEquivalence X' Y').inverse) (prodEquivalence_inverse_comp_functor X Y)).symm.trans
    (congrArg ((prodEquivalence X Y).inverse ⋙ ·)
      ((congrArg (· ⋙ (prodEquivalence X' Y').inverse)
        (prodEquivalence_functor_naturality f g).symm).trans
        (congrArg ((oneTruncation.map (prod.map f g)).toFunctor ⋙ ·)
          (prodEquivalence_functor_comp_inverse X' Y'))))

private def ballVertex : (DiagSet.toSSet.obj (ball.{u} atomPoint)) _⦋0⦌ :=
  ULift.up (toAtomPoint _)

noncomputable def isTerminalBall : IsTerminal (oneTruncation.obj (ball.{u} atomPoint)) :=
  Cat.chosenTerminalIsTerminal.{u, u}.ofIso
    { hom := Cat.Hom.ofFunctor ((Functor.const _).obj (mk ballVertex))
      inv := Cat.chosenTerminalIsTerminal.{u, u}.from _
      hom_inv_id := Cat.chosenTerminalIsTerminal.{u, u}.hom_ext _ _
      inv_hom_id := Cat.Hom.ext (functor_ext fun x y e => by
        refine (congrArg Arrow.mk (homMk_id ballVertex)).symm.trans ?_
        exact arrowMk_homMk_eq _ _ (ULift.ext _ _ (Subsingleton.elim (α := _ ⟶ atomPoint) _ _))) }

end OneTruncation

open OneTruncation in
instance (X Y : DiagSet.{u}) : PreservesLimit (pair X Y) oneTruncation.{u} :=
  preservesLimit_of_preserves_limit_cone (prodIsProd X Y)
    ((isLimitMapConeBinaryFanEquiv _ _ _).symm (IsLimit.ofIsoLimit (Cat.isLimitProdCone _ _)
      (BinaryFan.ext
        { hom := (prodEquivalence X Y).inverse.toCatHom
          inv := (prodEquivalence X Y).functor.toCatHom
          hom_inv_id := Cat.Hom.ext (prodEquivalence_inverse_comp_functor X Y)
          inv_hom_id := Cat.Hom.ext (prodEquivalence_functor_comp_inverse X Y) }
        (Cat.Hom.ext (congrArg (· ⋙ CategoryTheory.Prod.fst _ _)
          (prodEquivalence_inverse_comp_functor X Y)).symm)
        (Cat.Hom.ext (congrArg (· ⋙ CategoryTheory.Prod.snd _ _)
          (prodEquivalence_inverse_comp_functor X Y)).symm))))

instance : PreservesLimit (Functor.empty.{0} DiagSet.{u}) oneTruncation.{u} :=
  preservesLimit_of_preserves_limit_cone isTerminalBallAtomPoint
    ((isLimitMapConeEmptyConeEquiv _ _).symm OneTruncation.isTerminalBall)

instance : PreservesFiniteProducts oneTruncation.{u} :=
  have : PreservesLimitsOfShape (Discrete WalkingPair) oneTruncation.{u} :=
    ⟨fun {K} => preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm⟩
  have := preservesLimitsOfShape_pempty_of_preservesTerminal oneTruncation.{u}
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

noncomputable instance : oneTruncation.{u}.Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

section Nerve

open OneTruncation

private theorem curry_obj_prod_comp {B C D E F : Type*} [Category* B] [Category* C] [Category* D]
    [Category* E] [Category* F] (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ F) :
    Functor.curry.obj (F₁.prod F₂ ⋙ G) =
      F₁ ⋙ Functor.curry.obj G ⋙ (Functor.whiskeringLeft _ _ _).obj F₂ := by
  rw [← Functor.uncurry_obj_curry_obj_flip_flip', Functor.curry_obj_uncurry_obj]
  rfl

private noncomputable def prodFunctorEquiv (X Y : DiagSet.{u}) (D : Cat.{u, u}) :
    (oneTruncation.obj (X ⨯ Y) ⟶ D) ≃ (OneTruncation X × OneTruncation Y ⥤ D) where
  toFun G := (prodEquivalence X Y).inverse ⋙ G.toFunctor
  invFun H := Cat.Hom.ofFunctor ((prodEquivalence X Y).functor ⋙ H)
  left_inv G := Cat.Hom.ext (congrArg (· ⋙ G.toFunctor) (prodEquivalence_functor_comp_inverse X Y))
  right_inv H := congrArg (· ⋙ H) (prodEquivalence_inverse_comp_functor X Y)

noncomputable def categoricalNerveProdEquiv (A T : DiagSet.{u}) (D : Cat.{u, u}) :
    (T ⨯ A ⟶ categoricalNerve.obj D) ≃
      (T ⟶ categoricalNerve.obj (Cat.of (OneTruncation A ⥤ D))) :=
  (oneTruncationAdjunction.homEquiv _ _).symm.trans <| (prodFunctorEquiv T A D).trans <|
    Functor.curryingEquiv.symm.trans <|
      (Cat.Hom.equivFunctor (oneTruncation.obj T) (Cat.of (OneTruncation A ⥤ D))).symm.trans
        (oneTruncationAdjunction.homEquiv _ _)

private theorem categoricalNerveProdEquiv_apply (A T : DiagSet.{u}) (D : Cat.{u, u})
    (f : T ⨯ A ⟶ categoricalNerve.obj D) :
    categoricalNerveProdEquiv A T D f = oneTruncationAdjunction.homEquiv _ _ (Cat.Hom.ofFunctor
      (Functor.curry.obj ((prodEquivalence T A).inverse ⋙
        ((oneTruncationAdjunction.homEquiv _ _).symm f).toFunctor))) :=
  rfl

theorem categoricalNerveProdEquiv_naturality (A : DiagSet.{u}) (D : Cat.{u, u})
    {T T' : DiagSet.{u}} (t : T' ⟶ T) (f : T ⨯ A ⟶ categoricalNerve.obj D) :
    categoricalNerveProdEquiv A T' D (Limits.prod.map t (𝟙 A) ≫ f) =
      t ≫ categoricalNerveProdEquiv A T D f := by
  rw [categoricalNerveProdEquiv_apply, categoricalNerveProdEquiv_apply,
    ← Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left_symm]
  congr 1
  refine Cat.Hom.ext ?_
  change Functor.curry.obj (((prodEquivalence T' A).inverse ⋙
      (oneTruncation.map (prod.map t (𝟙 A))).toFunctor) ⋙
        ((oneTruncationAdjunction.homEquiv _ _).symm f).toFunctor) = _
  rw [← prodEquivalence_inverse_naturality t (𝟙 A), oneTruncation.map_id]
  exact curry_obj_prod_comp (oneTruncation.map t).toFunctor (𝟭 (OneTruncation A))
    ((prodEquivalence T A).inverse ⋙ ((oneTruncationAdjunction.homEquiv _ _).symm f).toFunctor)

theorem categoricalNerveProdEquiv_comp (A T : DiagSet.{u}) {D D' : Cat.{u, u}} (g : D ⟶ D')
    (f : T ⨯ A ⟶ categoricalNerve.obj D) :
    categoricalNerveProdEquiv A T D' (f ≫ categoricalNerve.map g) =
      categoricalNerveProdEquiv A T D f ≫
        categoricalNerve.map ((Functor.whiskeringRight _ _ _).obj g.toFunctor).toCatHom := by
  rw [categoricalNerveProdEquiv_apply, categoricalNerveProdEquiv_apply,
    ← Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right_symm]
  rfl

theorem categoricalNerveProdEquiv_precomp {A A' : DiagSet.{u}} (a : A' ⟶ A) (T : DiagSet.{u})
    (D : Cat.{u, u}) (f : T ⨯ A ⟶ categoricalNerve.obj D) :
    categoricalNerveProdEquiv A' T D (Limits.prod.map (𝟙 T) a ≫ f) =
      categoricalNerveProdEquiv A T D f ≫
        categoricalNerve.map ((Functor.whiskeringLeft _ _ _).obj
          (oneTruncation.map a).toFunctor).toCatHom := by
  rw [categoricalNerveProdEquiv_apply, categoricalNerveProdEquiv_apply,
    Adjunction.homEquiv_naturality_left_symm]
  have h := (oneTruncationAdjunction.homEquiv_naturality_right (Cat.Hom.ofFunctor
    (Functor.curry.obj ((prodEquivalence T A).inverse ⋙
      ((oneTruncationAdjunction.homEquiv _ _).symm f).toFunctor)) :
        oneTruncation.obj T ⟶ Cat.of (OneTruncation A ⥤ D))
    ((Functor.whiskeringLeft _ _ _).obj (oneTruncation.map a).toFunctor).toCatHom)
  refine Eq.trans ?_ h
  congr 1
  refine Cat.Hom.ext ?_
  change Functor.curry.obj (((prodEquivalence T A').inverse ⋙
      (oneTruncation.map (prod.map (𝟙 T) a)).toFunctor) ⋙
        ((oneTruncationAdjunction.homEquiv _ _).symm f).toFunctor) = _
  rw [← prodEquivalence_inverse_naturality (𝟙 T) a, oneTruncation.map_id]
  exact curry_obj_prod_comp (𝟭 (OneTruncation T)) (oneTruncation.map a).toFunctor
    ((prodEquivalence T A).inverse ⋙ ((oneTruncationAdjunction.homEquiv _ _).symm f).toFunctor)

private noncomputable def functorCounitIso (C D : Cat.{u, u}) :
    Cat.of (OneTruncation (categoricalNerve.obj C) ⥤ D) ≅ Cat.of (C ⥤ D) :=
  have ε := asIso (oneTruncationAdjunction.counit.app C)
  { hom := ((Functor.whiskeringLeft _ _ _).obj ε.inv.toFunctor).toCatHom
    inv := ((Functor.whiskeringLeft _ _ _).obj ε.hom.toFunctor).toCatHom
    hom_inv_id := Cat.Hom.ext ((Functor.whiskeringLeft_obj_comp _ _).symm.trans
      ((congrArg (fun F => (Functor.whiskeringLeft _ _ _).obj (Cat.Hom.toFunctor F))
        ε.hom_inv_id).trans Functor.whiskeringLeft_obj_id))
    inv_hom_id := Cat.Hom.ext ((Functor.whiskeringLeft_obj_comp _ _).symm.trans
      ((congrArg (fun F => (Functor.whiskeringLeft _ _ _).obj (Cat.Hom.toFunctor F))
        ε.inv_hom_id).trans Functor.whiskeringLeft_obj_id)) }

noncomputable def categoricalNerveNerveProdEquiv (C D : Cat.{u, u}) (T : DiagSet.{u}) :
    (T ⨯ categoricalNerve.obj C ⟶ categoricalNerve.obj D) ≃
      (T ⟶ categoricalNerve.obj (Cat.of (C ⥤ D))) :=
  (categoricalNerveProdEquiv (categoricalNerve.obj C) T D).trans
    ((Iso.refl T).homCongr (categoricalNerve.mapIso (functorCounitIso C D)))

private noncomputable def prodIsoTensor (T A : DiagSet.{u}) : T ⨯ A ≅ A ⊗ T where
  hom := lift prod.snd prod.fst
  inv := prod.lift (snd A T) (fst A T)
  hom_inv_id := prod.hom_ext (by simp) (by simp)
  inv_hom_id := by rw [comp_lift, prod.lift_snd, prod.lift_fst, lift_fst_snd]

private theorem prodIsoTensor_hom_naturality {T T' : DiagSet.{u}} (A : DiagSet.{u})
    (t : T' ⟶ T) :
    (prodIsoTensor T' A).hom ≫ A ◁ t = prod.map t (𝟙 A) ≫ (prodIsoTensor T A).hom := by
  simp [prodIsoTensor]

noncomputable def categoricalNerveExpIso (A : DiagSet.{u}) (D : Cat.{u, u}) :
    (ihom A).obj (categoricalNerve.obj D) ≅
      categoricalNerve.obj (Cat.of (OneTruncation A ⥤ D)) :=
  Yoneda.ext _ _
    (fun {T} f => categoricalNerveProdEquiv A T D
      ((prodIsoTensor T A).hom ≫ ((ihom.adjunction A).homEquiv _ _).symm f))
    (fun {T} g => (ihom.adjunction A).homEquiv _ _
      ((prodIsoTensor T A).inv ≫ (categoricalNerveProdEquiv A T D).symm g))
    (fun f => by simp)
    (fun g => by simp)
    (fun {T T'} t f => by
      rw [Adjunction.homEquiv_naturality_left_symm, ← categoricalNerveProdEquiv_naturality]
      congr 1
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ ((ihom.adjunction A).homEquiv _ _).symm f)
          (prodIsoTensor_hom_naturality A t)).trans (Category.assoc _ _ _)))

end Nerve

end Atoms.Diagrammatic

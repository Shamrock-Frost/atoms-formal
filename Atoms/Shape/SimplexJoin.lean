import Atoms.Shape.Cone

open CategoryTheory Atoms.Molecule Atoms.Molecule.OGP Simplicial AugmentedSimplexCategory

namespace Atoms.Shape

def atomSimplexJoinIso (m n : ℕ) :
    atomJoin (atomSimplex m) (atomSimplex n) ≅ atomSimplex (m + n + 1) :=
  Atom.isoOfIso ((FiniteOGP.ofOGPIso (join (atomSimplex m).ogp (atomSimplex n).ogp)).symm ≪≫
      join.mapIso (Iso.refl _) (FiniteOGP.ofOGPIso (simplex n)).symm ≪≫
      coneJoinSimplexIso (atomSimplex m) n) ≪≫
    (coneFunctor (n + 1)).mapIso (coneAtomPointIso m).symm ≪≫
    coneAssoc atomPoint m (n + 1) ≪≫ coneAtomPointIso (m + (n + 1))

private theorem conePointVertices_ordinalSum (m n : ℕ) (b : WithBot atomPoint.ogp)
    (T : Finset (Fin m)) (S : Finset (Fin (n + 1))) :
    conePointVertices (m + (n + 1))
        (b, T.map (Fin.castAddEmb (n + 1)) ∪ S.map (Fin.natAddEmb m)) =
      (conePointVertices m (b, T)).image (inl' ⦋m⦌ ⦋n⦌).toOrderHom ∪
        S.image (inr' ⦋m⦌ ⦋n⦌).toOrderHom := by
  have hl : ∀ i : Fin (m + 1), ((inl' ⦋m⦌ ⦋n⦌).toOrderHom i : ℕ) = i := fun i => by
    rw [inl'_eval]
    rfl
  have h0 : (inl' ⦋m⦌ ⦋n⦌).toOrderHom 0 = 0 := Fin.ext (hl 0)
  have h1 : (fun i : Fin m => (inl' ⦋m⦌ ⦋n⦌).toOrderHom (Fin.succ i)) =
      fun i => Fin.succ (Fin.castAdd (n + 1) i) :=
    funext fun i => Fin.ext ((hl _).trans (by simp))
  have h2 : ⇑(inr' ⦋m⦌ ⦋n⦌).toOrderHom = fun j => Fin.succ (Fin.natAdd m j) := by
    refine funext fun j => Fin.ext ?_
    rw [inr'_eval]
    simp only [SimplexCategory.len_mk, Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
    omega
  simp only [conePointVertices, Finset.map_eq_image, Finset.image_union, Finset.image_image,
    Function.comp_def, Fin.coe_succEmb, Fin.coe_castAddEmb, Fin.natAddEmb_apply, h1, h2]
  rw [Finset.union_assoc]
  congr 1
  split_ifs <;> simp [h0]

theorem atomSimplexVertices_atomSimplexJoinIso_hom (m n : ℕ)
    (z : (atomJoin (atomSimplex m) (atomSimplex n)).ogp) :
    atomSimplexVertices (m + n + 1) ((atomSimplexJoinIso m n).hom z) =
      (botVertices m (((FiniteOGP.ofOGPIso (join (atomSimplex m).ogp (atomSimplex n).ogp)).inv
          z).1.1.map (FiniteOGP.ofOGPIso (simplex m)).inv)).image (inl' ⦋m⦌ ⦋n⦌).toOrderHom ∪
      (botVertices n (((FiniteOGP.ofOGPIso (join (atomSimplex m).ogp (atomSimplex n).ogp)).inv
          z).1.2.map (FiniteOGP.ofOGPIso (simplex n)).inv)).image (inr' ⦋m⦌ ⦋n⦌).toOrderHom := by
  set p := (FiniteOGP.ofOGPIso (join (atomSimplex m).ogp (atomSimplex n).ogp)).inv z
  set S := botVertices n (p.1.2.map (FiniteOGP.ofOGPIso (simplex n)).inv)
  set a : WithBot (cone atomPoint m).ogp := p.1.1.map (coneAtomPointIso m).inv
  set y : (cone (atomSimplex m) (n + 1)).ogp :=
    (coneJoinSimplexIso (atomSimplex m) n).hom (joinMap id (FiniteOGP.ofOGPIso (simplex n)).inv p)
  set w : (cone (cone atomPoint m) (n + 1)).ogp := coneMap (coneAtomPointIso m).inv (n + 1) y
  have hw : coneCoord (cone atomPoint m) (n + 1) (w : WithBot _) = (a, S) := by
    refine (coneCoord_coneMap (coneAtomPointIso m).inv (n + 1) (y : WithBot _)).trans ?_
    rw [coneCoord_coneJoinSimplexIso]
    exact Prod.ext (congrArg (WithBot.map _) (congrFun WithBot.map_id p.1.1)) rfl
  have ha : botVertices m (p.1.1.map (FiniteOGP.ofOGPIso (simplex m)).inv) =
      conePointVertices m (coneCoord atomPoint m a) := by
    refine Eq.trans ?_ (botVertices_coneAtomPointIso m a)
    rw [WithBot.map_map]
    exact congrArg (fun φ => botVertices m (WithBot.map φ p.1.1))
      (funext fun x => congrArg _ (Iso.inv_hom_id_apply (coneAtomPointIso m) x).symm)
  refine (botVertices_coneAtomPointIso (m + (n + 1))
    (some ((coneAssoc atomPoint m (n + 1)).hom w))).trans ?_
  have hc := coneCoord_coneAssoc atomPoint m (n + 1) (w : WithBot _)
  rw [hw] at hc
  change conePointVertices _ (coneCoord atomPoint (m + (n + 1))
    ((w : WithBot _).map (coneAssoc atomPoint m (n + 1)).hom)) = _
  rw [hc, ha, conePointVertices_ordinalSum]

private theorem atomSimplexVertices_atomSimplexJoinIso_hom_ofOGPIso (m n : ℕ)
    (p : join (atomSimplex m).ogp (atomSimplex n).ogp) :
    atomSimplexVertices (m + n + 1) ((atomSimplexJoinIso m n).hom
      ((FiniteOGP.ofOGPIso (join (atomSimplex m).ogp (atomSimplex n).ogp)).hom p)) =
      (botVertices m (p.1.1.map (FiniteOGP.ofOGPIso (simplex m)).inv)).image
          (inl' ⦋m⦌ ⦋n⦌).toOrderHom ∪
        (botVertices n (p.1.2.map (FiniteOGP.ofOGPIso (simplex n)).inv)).image
          (inr' ⦋m⦌ ⦋n⦌).toOrderHom :=
  (atomSimplexVertices_atomSimplexJoinIso_hom m n _).trans (by rw [Iso.hom_inv_id_apply])

private theorem botVertices_map_simplexHom {m m' : ℕ} (σ : Fin (m + 1) →o Fin (m' + 1))
    (a : WithBot (atomSimplex m).ogp) :
    botVertices m' ((a.map (simplexHom σ)).map (FiniteOGP.ofOGPIso (simplex m')).inv) =
      (botVertices m (a.map (FiniteOGP.ofOGPIso (simplex m)).inv)).image σ := by
  induction a using WithBot.recBotCoe with
  | bot =>
    change botVertices m' ⊥ = (botVertices m ⊥).image σ
    rw [botVertices_bot, botVertices_bot, Finset.image_empty]
  | coe x => exact atomSimplexVertices_simplexHom σ x

private theorem image_image_toOrderHom {m m' k : ℕ} (f : ⦋m⦌ ⟶ ⦋m'⦌) (g : ⦋m'⦌ ⟶ ⦋k⦌)
    (A : Finset (Fin (m + 1))) :
    (A.image f.toOrderHom).image g.toOrderHom = A.image (f ≫ g).toOrderHom := by
  rw [Finset.image_image]
  rfl

@[reassoc] theorem joinHom_comp_atomSimplexJoinIso_hom {m m' n n' : ℕ}
    (f : ⦋m⦌ ⟶ ⦋m'⦌) (g : ⦋n⦌ ⟶ ⦋n'⦌) :
    joinHom (simplexFunctor.map f) (simplexFunctor.map g) ≫ (atomSimplexJoinIso m' n').hom =
      (atomSimplexJoinIso m n).hom ≫ simplexFunctor.map (tensorHomOf f g) := by
  refine Atom.hom_ext fun z => atomSimplexVertices_injective _ ?_
  set p : join (atomSimplex m).ogp (atomSimplex n).ogp :=
    (FiniteOGP.ofOGPIso (join (atomSimplex m).ogp (atomSimplex n).ogp)).inv z
  refine (atomSimplexVertices_atomSimplexJoinIso_hom_ofOGPIso m' n'
    (joinMap (simplexHom f.toOrderHom) (simplexHom g.toOrderHom) p)).trans
    (Eq.trans ?_ ((atomSimplexVertices_simplexHom (tensorHomOf f g).toOrderHom
      ((atomSimplexJoinIso m n).hom z)).trans
        (congrArg _ (atomSimplexVertices_atomSimplexJoinIso_hom m n z))).symm)
  rw [joinMap_val]
  dsimp only
  rw [botVertices_map_simplexHom, botVertices_map_simplexHom, Finset.image_union,
    image_image_toOrderHom, image_image_toOrderHom, image_image_toOrderHom,
    image_image_toOrderHom, inl'_comp_tensorHomOf, inr'_comp_tensorHomOf]

@[reassoc] theorem joinInclLeftHom_comp_atomSimplexJoinIso_hom (m n : ℕ) :
    joinInclLeftHom (atomSimplex m) (atomSimplex n) ≫ (atomSimplexJoinIso m n).hom =
      simplexFunctor.map (inl' ⦋m⦌ ⦋n⦌) := by
  refine Atom.hom_ext fun x => atomSimplexVertices_injective _ ?_
  have hx : (FiniteOGP.ofOGPIso (join (atomSimplex m).ogp (atomSimplex n).ogp)).inv
      (joinInclLeftHom (atomSimplex m) (atomSimplex n) x) = joinInclLeft _ _ x :=
    Iso.hom_inv_id_apply _ _
  rw [ConcreteCategory.comp_apply, atomSimplexVertices_atomSimplexJoinIso_hom, hx,
    simplexFunctor_map, atomSimplexVertices_simplexHom]
  exact (congrArg (_ ∪ ·) ((congrArg (Finset.image _) (botVertices_bot n)).trans
    (Finset.image_empty _))).trans (Finset.union_empty _)

@[reassoc] theorem joinInclRightHom_comp_atomSimplexJoinIso_hom (m n : ℕ) :
    joinInclRightHom (atomSimplex m) (atomSimplex n) ≫ (atomSimplexJoinIso m n).hom =
      simplexFunctor.map (inr' ⦋m⦌ ⦋n⦌) := by
  refine Atom.hom_ext fun x => atomSimplexVertices_injective _ ?_
  have hx : (FiniteOGP.ofOGPIso (join (atomSimplex m).ogp (atomSimplex n).ogp)).inv
      (joinInclRightHom (atomSimplex m) (atomSimplex n) x) = joinInclRight _ _ x :=
    Iso.hom_inv_id_apply _ _
  rw [ConcreteCategory.comp_apply, atomSimplexVertices_atomSimplexJoinIso_hom, hx,
    simplexFunctor_map, atomSimplexVertices_simplexHom]
  exact (congrArg (· ∪ _) ((congrArg (Finset.image _) (botVertices_bot m)).trans
    (Finset.image_empty _))).trans (Finset.empty_union _)

def simplexJoinNatIso :
    simplexFunctor.prod simplexFunctor ⋙ joinFunctor ≅ ordinalSum ⋙ simplexFunctor :=
  NatIso.ofComponents (fun p => atomSimplexJoinIso p.1.len p.2.len)
    fun f => joinHom_comp_atomSimplexJoinIso_hom f.1 f.2

end Atoms.Shape

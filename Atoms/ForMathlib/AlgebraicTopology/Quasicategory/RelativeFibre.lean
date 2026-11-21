import Atoms.ForMathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.SimplexFibre
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.MapOver

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed HomotopicalAlgebra

universe u

namespace SSet

noncomputable def simplicialRelativeRestrict {T S T' S' : SSet.{u}}
    (i : T ⟶ S) (j : T' ⟶ S') (t : T' ⟶ T) (s : S' ⟶ S)
    (h : j ≫ s = t ≫ i) (Q : SSet.{u}) (b : Δ[0] ⟶ (ihom T).obj Q) :
    pullback ((pre i).app Q) b ⟶
      pullback ((pre j).app Q) (b ≫ (pre t).app Q) :=
  pullback.map _ _ _ _ ((pre s).app Q) (𝟙 _) ((pre t).app Q)
    (by rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map, ← h])
    (Category.id_comp _).symm

noncomputable def simplicialRelativeTargetMap {T S : SSet.{u}} (i : T ⟶ S)
    {Q Q' : SSet.{u}} (f : Q ⟶ Q') (b : Δ[0] ⟶ (ihom T).obj Q) :
    pullback ((pre i).app Q) b ⟶
      pullback ((pre i).app Q') (b ≫ (ihom T).map f) :=
  pullback.map _ _ _ _ ((ihom S).map f) (𝟙 _) ((ihom T).map f)
    (pre_comm_ihom_map i f).symm (Category.id_comp _).symm

private noncomputable def isLimitFanPre {p : ℕ} (K : Fin (p + 1) → SSet.{u}) (Q : SSet.{u}) :
    IsLimit (Fan.mk ((ihom (∐ K)).obj Q) fun k => (pre (Sigma.ι K k)).app Q) :=
  Fan.IsLimit.mk _
    (fun s => curry (Cofan.IsColimit.desc
      (isColimitOfHasCoproductOfPreservesColimit (MonoidalCategory.tensorRight s.pt) K)
      fun k => uncurry (s.proj k)))
    (fun s k => by
      change curry _ ≫ (pre (Sigma.ι K k)).app Q = s.proj k
      rw [curry_pre_app]
      simpa only [cofan_mk_inj, MonoidalCategory.tensorRight, MonoidalCategory.curriedTensor,
        Functor.flip, curry_uncurry] using congrArg curry (Cofan.IsColimit.fac
        (isColimitOfHasCoproductOfPreservesColimit (MonoidalCategory.tensorRight s.pt) K)
        (fun k => uncurry (s.proj k)) k))
    (fun s m hm => by
      apply uncurry_injective
      refine Cofan.IsColimit.hom_ext
        (isColimitOfHasCoproductOfPreservesColimit (MonoidalCategory.tensorRight s.pt) K)
        _ _ fun k => ?_
      change (Sigma.ι K k) ▷ s.pt ≫ uncurry m =
        (Sigma.ι K k) ▷ s.pt ≫ uncurry (curry _)
      have hmk : m ≫ (pre (Sigma.ι K k)).app Q = s.proj k := hm k
      rw [← uncurry_pre_app, hmk, uncurry_curry]
      simpa only [cofan_mk_inj, MonoidalCategory.tensorRight,
        MonoidalCategory.curriedTensor, Functor.flip] using (Cofan.IsColimit.fac
        (isColimitOfHasCoproductOfPreservesColimit (MonoidalCategory.tensorRight s.pt) K)
        (fun k => uncurry (s.proj k)) k).symm)

noncomputable def ihomVerticesIso (p : ℕ) (Q : SSet.{u}) :
    (ihom (∐ fun _ : Fin (p + 1) => (Δ[0] : SSet.{u}))).obj Q ≅
      ∏ᶜ fun _ : Fin (p + 1) => Q :=
  (isLimitFanPre (fun _ : Fin (p + 1) => (Δ[0] : SSet.{u})) Q).conePointUniqueUpToIso
    (limit.isLimit _) ≪≫ Pi.mapIso (fun _ => SSet.ihomStdSimplexZeroIso Q)

@[reassoc]
theorem ihomVerticesIso_hom_π (p : ℕ) (Q : SSet.{u}) (k : Fin (p + 1)) :
    (ihomVerticesIso p Q).hom ≫ Pi.π _ k =
      (pre (Sigma.ι (fun _ : Fin (p + 1) => (Δ[0] : SSet.{u})) k)).app Q ≫
        SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q := by
  rw [ihomVerticesIso, Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
    ← Category.assoc, ← SSet.ihomStdSimplexZeroIso_hom_eq_evalVertex]
  exact congrArg (· ≫ (SSet.ihomStdSimplexZeroIso Q).hom)
    (IsLimit.conePointUniqueUpToIso_hom_comp
      (isLimitFanPre (fun _ : Fin (p + 1) => (Δ[0] : SSet.{u})) Q)
      (limit.isLimit _) (Discrete.mk k))

noncomputable def simplicialShapeVerticesι {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) :
    (∐ fun _ : Fin (p + 1) => (Δ[0] : SSet.{u})) ⟶ S :=
  Sigma.desc fun k => SSet.yonedaEquiv.symm (v k)

theorem pre_simplicialShapeVerticesι_comp_ihomVerticesIso {S : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (Q : SSet.{u}) :
    (pre (simplicialShapeVerticesι v)).app Q ≫ (ihomVerticesIso p Q).hom =
      SSet.ihomEvalVertices v Q := by
  apply Pi.hom_ext
  intro k
  rw [Category.assoc, ihomVerticesIso_hom_π, ← Category.assoc,
    ← NatTrans.comp_app, ← pre_map, simplicialShapeVerticesι, Sigma.ι_desc,
    SSet.pre_app_comp_evalVertex, SSet.ihomEvalVertices_π]
  congr 1
  exact (SSet.yonedaEquiv_comp (𝟙 Δ[0]) (SSet.yonedaEquiv.symm (v k))).symm.trans
    (by rw [Category.id_comp, Equiv.apply_symm_apply])

noncomputable def simplicialVertexFibreTargetMap {S Q Q' : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (f : Q ⟶ Q') (c : Fin (p + 1) → Q _⦋0⦌) :
    SSet.ihomFibre v Q c ⟶ SSet.ihomFibre v Q' (fun k => f.app _ (c k)) :=
  SSet.ihomFibre.lift (SSet.ihomFibre.ι v Q c ≫ (ihom S).map f) fun k => by
    rw [Category.assoc, SSet.ihom_map_comp_evalVertex, SSet.ihomFibre.ι_evalVertex_assoc,
      SSet.const_comp]

@[reassoc]
theorem simplicialVertexFibreTargetMap_ι {S Q Q' : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (f : Q ⟶ Q') (c : Fin (p + 1) → Q _⦋0⦌) :
    simplicialVertexFibreTargetMap v f c ≫ SSet.ihomFibre.ι v Q' (fun k => f.app _ (c k)) =
      SSet.ihomFibre.ι v Q c ≫ (ihom S).map f :=
  SSet.ihomFibre.lift_ι _ _

theorem ihomEvalVertices_target {S Q Q' : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (f : Q ⟶ Q') :
    (ihom S).map f ≫ SSet.ihomEvalVertices v Q' =
      SSet.ihomEvalVertices v Q ≫ Limits.Pi.map (fun _ => f) := by
  apply Pi.hom_ext
  intro k
  rw [Category.assoc, SSet.ihomEvalVertices_π, SSet.ihom_map_comp_evalVertex,
    Category.assoc, Limits.Pi.map_π, SSet.ihomEvalVertices_π_assoc]

noncomputable def simplicialVertexFibreTargetMapOfEq {S Q Q' : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (f : Q ⟶ Q')
    (c : Fin (p + 1) → Q _⦋0⦌) (d : Fin (p + 1) → Q' _⦋0⦌)
    (h : ∀ k, f.app _ (c k) = d k) : SSet.ihomFibre v Q c ⟶ SSet.ihomFibre v Q' d :=
  simplicialVertexFibreTargetMap v f c ≫ eqToHom (congrArg (SSet.ihomFibre v Q') (funext h))

@[reassoc]
theorem simplicialVertexFibreTargetMapOfEq_ι {S Q Q' : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (f : Q ⟶ Q')
    (c : Fin (p + 1) → Q _⦋0⦌) (d : Fin (p + 1) → Q' _⦋0⦌)
    (h : ∀ k, f.app _ (c k) = d k) :
    simplicialVertexFibreTargetMapOfEq v f c d h ≫ SSet.ihomFibre.ι v Q' d =
      SSet.ihomFibre.ι v Q c ≫ (ihom S).map f := by
  obtain rfl : (fun k => f.app _ (c k)) = d := funext h
  exact simplicialVertexFibreTargetMap_ι v f c

theorem simplicialVertexFibreTargetMapOfEq_restrict {S S' Q Q' : SSet.{u}} {p q : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (v' : Fin (q + 1) → S' _⦋0⦌)
    (s : S' ⟶ S) (φ : Fin (q + 1) → Fin (p + 1))
    (hv : ∀ k, s.app _ (v' k) = v (φ k)) (f : Q ⟶ Q')
    (c : Fin (p + 1) → Q _⦋0⦌) (d : Fin (p + 1) → Q' _⦋0⦌)
    (h : ∀ k, f.app _ (c k) = d k) :
    simplicialVertexFibreTargetMapOfEq v f c d h ≫ SSet.ihomFibre.map s φ hv Q' d =
      SSet.ihomFibre.map s φ hv Q c ≫
        simplicialVertexFibreTargetMapOfEq v' f (c ∘ φ) (d ∘ φ) (fun k => h (φ k)) := by
  apply SSet.ihomFibre.hom_ext
  rw [Category.assoc, SSet.ihomFibre.map_ι,
    simplicialVertexFibreTargetMapOfEq_ι_assoc, Category.assoc,
    simplicialVertexFibreTargetMapOfEq_ι, SSet.ihomFibre.map_ι_assoc]
  exact congrArg (SSet.ihomFibre.ι v Q c ≫ ·) (pre_comm_ihom_map s f).symm

theorem simplicialVertexFibreTargetMapOfEq_square {S Q₀ Q₁ Q₂ Q₃ : SSet.{u}} {p : ℕ}
    (v : Fin (p + 1) → S _⦋0⦌) (f : Q₀ ⟶ Q₁) (g : Q₁ ⟶ Q₃)
    (f' : Q₀ ⟶ Q₂) (g' : Q₂ ⟶ Q₃) (w : f ≫ g = f' ≫ g')
    (c₀ : Fin (p + 1) → Q₀ _⦋0⦌) (c₁ : Fin (p + 1) → Q₁ _⦋0⦌)
    (c₂ : Fin (p + 1) → Q₂ _⦋0⦌) (c₃ : Fin (p + 1) → Q₃ _⦋0⦌)
    (h₀₁ : ∀ k, f.app _ (c₀ k) = c₁ k) (h₁₃ : ∀ k, g.app _ (c₁ k) = c₃ k)
    (h₀₂ : ∀ k, f'.app _ (c₀ k) = c₂ k) (h₂₃ : ∀ k, g'.app _ (c₂ k) = c₃ k) :
    simplicialVertexFibreTargetMapOfEq v f c₀ c₁ h₀₁ ≫
        simplicialVertexFibreTargetMapOfEq v g c₁ c₃ h₁₃ =
      simplicialVertexFibreTargetMapOfEq v f' c₀ c₂ h₀₂ ≫
        simplicialVertexFibreTargetMapOfEq v g' c₂ c₃ h₂₃ := by
  apply SSet.ihomFibre.hom_ext
  simp only [Category.assoc, simplicialVertexFibreTargetMapOfEq_ι,
    simplicialVertexFibreTargetMapOfEq_ι_assoc, ← Functor.map_comp, w]

instance mono_simplicialShapeVerticesι_simplex (p : ℕ) :
    Mono (simplicialShapeVerticesι (SSet.stdSimplex.obj₀Equiv.symm :
      Fin (p + 1) → (Δ[p] : SSet.{u}) _⦋0⦌)) := by
  have (k : Fin (p + 1)) : Mono (SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm k) : (Δ[0] : SSet.{u}) ⟶ Δ[p]) :=
    SSet.stdSimplex.isTerminalObj₀.mono_from _
  apply FunctorToTypes.mono_sigmaDesc_of_disjoint
  intro U j k t t' h
  exact congrArg (fun z : (Δ[p] : SSet.{u}).obj U => z.down.toOrderHom 0) h

theorem simplicialShapeVerticesι_spine_comp (p : ℕ) :
    simplicialShapeVerticesι (SSet.spineSubcomplex.spineId p).vertex ≫
        (SSet.spineSubcomplex.{u} p).ι =
      simplicialShapeVerticesι (SSet.stdSimplex.obj₀Equiv.symm :
        Fin (p + 1) → (Δ[p] : SSet.{u}) _⦋0⦌) := by
  apply Sigma.hom_ext
  intro k
  rw [simplicialShapeVerticesι, Sigma.ι_desc_assoc, simplicialShapeVerticesι,
    Sigma.ι_desc, SSet.yonedaEquiv_symm_comp]
  rfl

instance mono_simplicialShapeVerticesι_spine (p : ℕ) :
    Mono (simplicialShapeVerticesι (SSet.spineSubcomplex.spineId.{u} p).vertex) := by
  have : Mono (simplicialShapeVerticesι (SSet.spineSubcomplex.spineId.{u} p).vertex ≫
      (SSet.spineSubcomplex p).ι) := by
    rw [simplicialShapeVerticesι_spine_comp]
    infer_instance
  exact mono_of_mono _ (SSet.spineSubcomplex p).ι

end SSet

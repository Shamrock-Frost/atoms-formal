import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FunctionSpace
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpace
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FinalObject
import Atoms.ForMathlib.CategoryTheory.Adhesive.Basic
import Atoms.ForMathlib.CategoryTheory.Monoidal.PushoutProduct

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed CartesianMonoidalCategory
  Opposite

universe u

namespace SSet

section BoundaryOne

private lemma boundary_one_obj_eq {n : ℕ} (x : (∂Δ[1] : SSet.{u}) _⦋n⦌) (j : Fin 2)
    (hj : j ∉ Set.range x.1) (i : Fin (n + 1)) : x.1 i = j.rev := by
  have : x.1 i ≠ j := fun h ↦ hj ⟨i, h⟩
  have key : ∀ j k : Fin 2, k ≠ j → k = j.rev := by decide
  exact key j _ this

private lemma boundary_ι_app_apply {n : ℕ} (j : Fin 2) (y : (Δ[0] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) : ((boundary.ι j).app _ y).1 i = j.rev := by
  change (SimplexCategory.δ j).toOrderHom (y i) = j.rev
  rw [Fin.eq_zero (y i)]
  fin_cases j <;> rfl

noncomputable def boundaryOneIsColimit :
    IsColimit (BinaryCofan.mk (boundary.ι 1 : Δ[0] ⟶ (∂Δ[1] : SSet.{u})) (boundary.ι 0)) := by
  refine evaluationJointlyReflectsColimits _ fun ⟨n⟩ ↦ ?_
  induction n using SimplexCategory.rec with | _ n => ?_
  refine (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm
    (Nonempty.some ((Types.binaryCofan_isColimit_iff _).2 ⟨fun _ _ _ ↦ ?_, fun _ _ _ ↦ ?_, ?_⟩))
  · exact stdSimplex.ext _ _ fun i ↦ (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  · exact stdSimplex.ext _ _ fun i ↦ (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  constructor
  · rw [Set.disjoint_iff]
    rintro x ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    have := (boundary_ι_app_apply 1 y 0).symm.trans
      ((congrArg (fun w ↦ w.1 0) hz).symm.trans (boundary_ι_app_apply 0 z 0))
    exact absurd this (by decide)
  · refine codisjoint_iff_le_sup.2 fun x _ ↦ ?_
    obtain ⟨j, hj⟩ := (mem_boundary_iff_notMem_range x.1).1 x.2
    have hx : ∀ k : Fin 2, j = k → ∃ y, (boundary.ι k).app (op ⦋n⦌) y = x := fun k hk ↦
      ⟨stdSimplex.objEquiv.symm (SimplexCategory.const _ _ 0), Subtype.ext (stdSimplex.ext _ _
        fun i ↦ (boundary_ι_app_apply k _ i).trans (by rw [boundary_one_obj_eq x j hj i, hk]))⟩
    rcases (show ∀ k : Fin 2, k = 1 ∨ k = 0 by decide) j with h | h
    · exact Or.inl (hx 1 h)
    · exact Or.inr (hx 0 h)

noncomputable def boundaryOneTensorIsColimit (T : SSet.{u}) :
    IsColimit (BinaryCofan.mk (boundary.ι 1 ▷ T : Δ[0] ⊗ T ⟶ (∂Δ[1] : SSet.{u}) ⊗ T)
      (boundary.ι 0 ▷ T)) :=
  isColimitMapCoconeBinaryCofanEquiv (tensorRight T) _ _
    (isColimitOfPreserves (tensorRight T) boundaryOneIsColimit)

noncomputable def boundaryOneTensorDesc {T Y : SSet.{u}} (f₀ f₁ : T ⟶ Y) :
    (∂Δ[1] : SSet.{u}) ⊗ T ⟶ Y :=
  (boundaryOneTensorIsColimit T).desc (BinaryCofan.mk (snd _ _ ≫ f₀) (snd _ _ ≫ f₁))

@[reassoc]
theorem boundary_ι_one_whiskerRight_boundaryOneTensorDesc {T Y : SSet.{u}}
    (f₀ f₁ : T ⟶ Y) : boundary.ι 1 ▷ T ≫ boundaryOneTensorDesc f₀ f₁ = snd _ _ ≫ f₀ :=
  (boundaryOneTensorIsColimit T).fac _ ⟨.left⟩

@[reassoc]
theorem boundary_ι_zero_whiskerRight_boundaryOneTensorDesc {T Y : SSet.{u}}
    (f₀ f₁ : T ⟶ Y) : boundary.ι 0 ▷ T ≫ boundaryOneTensorDesc f₀ f₁ = snd _ _ ≫ f₁ :=
  (boundaryOneTensorIsColimit T).fac _ ⟨.right⟩

theorem boundaryOneTensor_hom_ext {T Y : SSet.{u}} {f g : (∂Δ[1] : SSet.{u}) ⊗ T ⟶ Y}
    (h₁ : boundary.ι 1 ▷ T ≫ f = boundary.ι 1 ▷ T ≫ g)
    (h₀ : boundary.ι 0 ▷ T ≫ f = boundary.ι 0 ▷ T ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (boundaryOneTensorIsColimit T) h₁ h₀

end BoundaryOne

section Map

variable {X Y Z : SSet.{u}}

@[reassoc]
private lemma ihomStdSimplexOneEval_comp_tensorHom (f : X ⟶ Y) :
    ihomStdSimplexOneEval X ≫ (f ⊗ₘ f) = (ihom Δ[1]).map f ≫ ihomStdSimplexOneEval Y := by
  ext1 <;> simp [ihomStdSimplexOneEval, ihom_map_comp_evalVertex]

private lemma lift_comp_tensorHom (f : X ⟶ Y) (x y : X _⦋0⦌) :
    lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) ≫ (f ⊗ₘ f) =
      𝟙 _ ≫ lift (yonedaEquiv.symm (f.app _ x)) (yonedaEquiv.symm (f.app _ y)) := by
  ext1 <;> simp

noncomputable def mappingSpaceMap (f : X ⟶ Y) (x y : X _⦋0⦌) :
    mappingSpace X x y ⟶ mappingSpace Y (f.app _ x) (f.app _ y) :=
  pullback.map _ _ _ _ ((ihom Δ[1]).map f) (𝟙 _) (f ⊗ₘ f)
    (ihomStdSimplexOneEval_comp_tensorHom f).symm (lift_comp_tensorHom f x y)

@[reassoc]
theorem mappingSpaceMap_fst (f : X ⟶ Y) (x y : X _⦋0⦌) :
    mappingSpaceMap f x y ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (ihom Δ[1]).map f :=
  pullback.lift_fst _ _ _

theorem mappingSpace_hom_ext {T : SSet.{u}} {x y : X _⦋0⦌} {g h : T ⟶ mappingSpace X x y}
    (e : g ≫ pullback.fst _ _ = h ≫ pullback.fst _ _) : g = h :=
  pullback.hom_ext e (stdSimplex.isTerminalObj₀.hom_ext _ _)

theorem mappingSpaceMap_id (X : SSet.{u}) (x y : X _⦋0⦌) : mappingSpaceMap (𝟙 X) x y = 𝟙 _ :=
  mappingSpace_hom_ext ((mappingSpaceMap_fst _ _ _).trans
    ((congrArg _ (CategoryTheory.Functor.map_id _ _)).trans
    ((Category.comp_id _).trans (Category.id_comp _).symm)))

theorem mappingSpaceMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x y : X _⦋0⦌) :
    mappingSpaceMap (f ≫ g) x y = mappingSpaceMap f x y ≫ mappingSpaceMap g _ _ :=
  mappingSpace_hom_ext ((mappingSpaceMap_fst _ _ _).trans ((Category.assoc _ _ _).trans
    ((congrArg (mappingSpaceMap f x y ≫ ·) (mappingSpaceMap_fst g _ _)).trans
      ((mappingSpaceMap_fst_assoc f x y ((ihom Δ[1]).map g)).trans ((Category.assoc _ _ _).trans
        (congrArg _ (CategoryTheory.Functor.map_comp _ _ _).symm))))).symm)

lemma mappingSpaceVerticesEquiv_map (f : X ⟶ Y) (x y : X _⦋0⦌)
    (v : (mappingSpace X x y) _⦋0⦌) :
    mappingSpaceVerticesEquiv Y _ _ ((mappingSpaceMap f x y).app _ v) =
      (mappingSpaceVerticesEquiv X x y v).map f := by
  apply Edge.ext
  rw [Edge.map_edge]
  rw [mappingSpaceVerticesEquiv_edge, mappingSpaceVerticesEquiv_edge]
  have h : yonedaEquiv.symm ((mappingSpaceMap f x y).app _ v) ≫ pullback.fst _ _ =
      (yonedaEquiv.symm v ≫ pullback.fst _ _) ≫ (ihom Δ[1]).map f := by
    exact (congrArg (· ≫ pullback.fst _ _)
      (yonedaEquiv_symm_comp v (mappingSpaceMap f x y)).symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (yonedaEquiv.symm v ≫ ·)
        (mappingSpaceMap_fst f x y)).trans (Category.assoc _ _ _).symm))
  rw [h, uncurry_natural_right, ← yonedaEquiv_comp, Category.assoc]

end Map

section TrivialFibration

variable {X Y : SSet.{u}}

lemma isofibration_pre_boundaryOne (A : SSet.{u}) [A.Quasicategory] :
    Isofibration ((pre (∂Δ[1]).ι).app A) :=
  isofibration_pullbackObjObjπ (terminal.from A) (∂Δ[1]).ι
    (Functor.PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal)

private noncomputable abbrev boundaryVertex (j : Fin 2) : (∂Δ[1] : SSet.{u}) _⦋0⦌ :=
  yonedaEquiv (boundary.ι j)

noncomputable def boundaryEval (X : SSet.{u}) : (ihom (∂Δ[1] : SSet.{u})).obj X ⟶ X ⊗ X :=
  lift (evalVertex (boundaryVertex 1) X) (evalVertex (boundaryVertex 0) X)

private lemma comp_evalVertex_boundaryVertex {T : SSet.{u}}
    (g : T ⟶ (ihom (∂Δ[1] : SSet.{u})).obj X) (j : Fin 2) : g ≫ evalVertex (boundaryVertex j) X =
      lift (stdSimplex.isTerminalObj₀.from T) (𝟙 T) ≫ boundary.ι j ▷ T ≫ uncurry g := by
  rw [comp_evalVertex, Equiv.symm_apply_apply, ← Category.assoc, lift_whiskerRight]

instance mono_boundaryEval (X : SSet.{u}) : Mono (boundaryEval X) := ⟨fun g h hgh ↦ by
  have hs (T : SSet.{u}) : snd Δ[0] T ≫ lift (stdSimplex.isTerminalObj₀.from T) (𝟙 T) = 𝟙 _ := by
    ext1
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
    · simp
  have e (j : Fin 2)
      (h₀ : g ≫ evalVertex (boundaryVertex j) X = h ≫ evalVertex (boundaryVertex j) X) :
      boundary.ι j ▷ _ ≫ uncurry g = boundary.ι j ▷ _ ≫ uncurry h := by
    rw [comp_evalVertex_boundaryVertex, comp_evalVertex_boundaryVertex] at h₀
    rw [← Category.id_comp (boundary.ι j ▷ _ ≫ uncurry g), ← hs, Category.assoc, h₀,
      ← Category.assoc,
      hs, Category.id_comp]
  have h₀ := congrArg (· ≫ fst X X) hgh
  have h₁ := congrArg (· ≫ snd X X) hgh
  simp only [Category.assoc, boundaryEval, lift_fst, lift_snd] at h₀ h₁
  exact uncurry_injective (boundaryOneTensor_hom_ext (e 1 h₀) (e 0 h₁))⟩

@[reassoc]
lemma pre_comp_boundaryEval (X : SSet.{u}) :
    (pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app X ≫ boundaryEval X =
      ihomStdSimplexOneEval X := by
  have e (j : Fin 2) : (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι.app _ (boundaryVertex j) =
      yonedaEquiv (stdSimplex.δ j) := by
    rw [← yonedaEquiv_comp, boundary.ι_ι]
  ext1
  · rw [Category.assoc, boundaryEval, lift_fst, pre_app_comp_evalVertex, e, stdSimplex_δ_one_eq,
      Equiv.apply_symm_apply, ihomStdSimplexOneEval, lift_fst]
  · rw [Category.assoc, boundaryEval, lift_snd, pre_app_comp_evalVertex, e, stdSimplex_δ_zero_eq,
      Equiv.apply_symm_apply, ihomStdSimplexOneEval, lift_snd]

noncomputable def boundaryPoint (x y : X _⦋0⦌) : Δ[0] ⟶ (ihom (∂Δ[1] : SSet.{u})).obj X :=
  curry (boundaryOneTensorDesc (yonedaEquiv.symm x) (yonedaEquiv.symm y))

@[reassoc]
lemma boundaryPoint_comp_boundaryEval (x y : X _⦋0⦌) :
    boundaryPoint x y ≫ boundaryEval X = lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) := by
  have e : lift (stdSimplex.isTerminalObj₀.from Δ[0]) (𝟙 Δ[0]) ≫ snd Δ[0] Δ[0] = 𝟙 _ := lift_snd _ _
  ext1
  · rw [Category.assoc, boundaryEval, lift_fst, comp_evalVertex_boundaryVertex, boundaryPoint,
      uncurry_curry, boundary_ι_one_whiskerRight_boundaryOneTensorDesc, reassoc_of% e, lift_fst]
  · rw [Category.assoc, boundaryEval, lift_snd, comp_evalVertex_boundaryVertex, boundaryPoint,
      uncurry_curry, boundary_ι_zero_whiskerRight_boundaryOneTensorDesc, reassoc_of% e, lift_snd]

lemma ihom_map_comp_boundaryEval (p : X ⟶ Y) :
    (ihom (∂Δ[1] : SSet.{u})).map p ≫ boundaryEval Y = boundaryEval X ≫ (p ⊗ₘ p) := by
  ext1 <;> simp [boundaryEval, ihom_map_comp_evalVertex]

@[reassoc]
lemma boundaryPoint_comp_ihom_map (p : X ⟶ Y) (x y : X _⦋0⦌) :
    boundaryPoint x y ≫ (ihom (∂Δ[1] : SSet.{u})).map p =
      boundaryPoint (p.app _ x) (p.app _ y) := by
  rw [← cancel_mono (boundaryEval Y), boundaryPoint_comp_boundaryEval, Category.assoc,
    ihom_map_comp_boundaryEval, boundaryPoint_comp_boundaryEval_assoc, lift_comp_tensorHom,
    Category.id_comp]

private lemma comp_ihomStdSimplexOneEval_eq_iff {T : SSet.{u}} (g : T ⟶ (ihom Δ[1]).obj X)
    (t : T ⟶ Δ[0]) (x y : X _⦋0⦌) :
    g ≫ ihomStdSimplexOneEval X = t ≫ lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) ↔
      g ≫ (pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app X = t ≫ boundaryPoint x y := by
  rw [← pre_comp_boundaryEval, ← boundaryPoint_comp_boundaryEval, ← Category.assoc,
    ← Category.assoc, cancel_mono]

lemma mappingSpace_fst_pre (x y : X _⦋0⦌) :
    (pullback.fst _ _ : mappingSpace X x y ⟶ _) ≫
        (pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app X =
      pullback.snd _ _ ≫ boundaryPoint x y :=
  (comp_ihomStdSimplexOneEval_eq_iff _ _ x y).1 pullback.condition

theorem isPullback_mappingSpace_pre (X : SSet.{u}) (x y : X _⦋0⦌) :
    IsPullback (pullback.fst _ _ : mappingSpace X x y ⟶ _) (pullback.snd _ _)
      ((pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app X) (boundaryPoint x y) :=
  IsPullback.of_isLimit' ⟨mappingSpace_fst_pre x y⟩ (PullbackCone.IsLimit.mk _
    (fun s => pullback.lift s.fst s.snd ((comp_ihomStdSimplexOneEval_eq_iff _ _ x y).2 s.condition))
    (fun _ => pullback.lift_fst _ _ _) (fun _ => pullback.lift_snd _ _ _)
    (fun _ _ h₁ h₂ => pullback.hom_ext (h₁.trans (pullback.lift_fst _ _ _).symm)
      (h₂.trans (pullback.lift_snd _ _ _).symm)))

theorem trivialFibration_mappingSpaceMap {p : X ⟶ Y} (hp : modelCategoryQuillen.I.rlp p)
    (x y : X _⦋0⦌) : modelCategoryQuillen.I.rlp (mappingSpaceMap p x y) := by
  let sq := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
    (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι p
  rw [← rlp_monomorphisms] at hp ⊢
  have hπ : (MorphismProperty.monomorphisms SSet.{u}).rlp sq.π := by
    intro A B i hi
    have : Mono i := hi
    have : Mono (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
        (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι i).ι :=
      MonoidalCategory.Arrow.mono_pushoutProduct (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι i
    exact (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) _ i) sq).1
      (hp _ (MorphismProperty.monomorphisms.infer_property _))
  intro A B i hi
  have := hπ i hi
  refine ⟨fun {t b} hsq ↦ ?_⟩
  let toB : B ⟶ Δ[0] := stdSimplex.isTerminalObj₀.from B
  have htB : toB = b ≫ pullback.snd _ _ := stdSimplex.isTerminalObj₀.hom_ext _ _
  have htA : i ≫ toB = t ≫ pullback.snd _ _ := stdSimplex.isTerminalObj₀.hom_ext _ _
  let b' : B ⟶ sq.pt := sq.isPullback.lift (toB ≫ boundaryPoint x y) (b ≫ pullback.fst _ _) (by
    refine (Category.assoc _ _ _).trans
      ((congrArg (toB ≫ ·) (boundaryPoint_comp_ihom_map p x y)).trans ?_)
    exact (congrArg (· ≫ boundaryPoint _ _) htB).trans ((Category.assoc _ _ _).trans
      ((congrArg (b ≫ ·) (mappingSpace_fst_pre _ _)).symm.trans (Category.assoc _ _ _).symm)))
  have hw : (t ≫ pullback.fst _ _) ≫ sq.π = i ≫ b' := by
    refine sq.isPullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq.π_fst).trans
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (mappingSpace_fst_pre x y)).trans
          (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) htA.symm)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (i ≫ ·) (sq.isPullback.lift_fst _ _ _).symm))))))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq.π_snd).trans
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (mappingSpaceMap_fst p x y)).symm.trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hsq.w).trans
            ((Category.assoc _ _ _).trans
              (congrArg (i ≫ ·) (sq.isPullback.lift_snd _ _ _).symm)))))))
  obtain ⟨l⟩ := (this.sq_hasLift (CommSq.mk hw)).exists_lift
  have hl : l.l ≫ ihomStdSimplexOneEval X = toB ≫ lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) :=
    (comp_ihomStdSimplexOneEval_eq_iff _ _ x y).2 ((congrArg (l.l ≫ ·) sq.π_fst).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) l.fac_right).trans
        (sq.isPullback.lift_fst _ _ _))))
  refine ⟨⟨⟨pullback.lift l.l toB hl, mappingSpace_hom_ext ?_, mappingSpace_hom_ext ?_⟩⟩⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) (pullback.lift_fst _ _ _)).trans
      l.fac_left)
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (mappingSpaceMap_fst p x y)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_fst _ _ _)).trans
        ((congrArg (l.l ≫ ·) sq.π_snd).symm.trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) l.fac_right).trans (sq.isPullback.lift_snd _ _ _)))))))

end TrivialFibration

theorem mappingSpaceVerticesEquiv_edge_yoneda {X : SSet.{u}} (x y : X _⦋0⦌)
    (v : (mappingSpace X x y) _⦋0⦌) :
    yonedaEquiv.symm (mappingSpaceVerticesEquiv X x y v).edge =
      ihomPointEquiv Δ[1] X (yonedaEquiv.symm ((pullback.fst
        (ihomStdSimplexOneEval X) (lift (yonedaEquiv.symm x) (yonedaEquiv.symm y))).app _ v)) :=
  (yonedaEquiv.symm_apply_apply _).trans
    (congrArg (ihomPointEquiv Δ[1] X) (yonedaEquiv_symm_comp v _))

noncomputable def mappingSpaceMapOfEq {Q Q' : SSet.{u}} (g : Q ⟶ Q') {a b : Q _⦋0⦌}
    {a' b' : Q' _⦋0⦌} (ha : g.app _ a = a') (hb : g.app _ b = b') :
    SSet.mappingSpace Q a b ⟶ SSet.mappingSpace Q' a' b' :=
  SSet.mappingSpaceMap g a b ≫ eqToHom (by rw [ha, hb])

@[reassoc]
theorem mappingSpaceMapOfEq_fst {Q Q' : SSet.{u}} (g : Q ⟶ Q') {a b : Q _⦋0⦌}
    {a' b' : Q' _⦋0⦌} (ha : g.app _ a = a') (hb : g.app _ b = b') :
    mappingSpaceMapOfEq g ha hb ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (ihom Δ[1]).map g := by
  subst ha hb
  rw [mappingSpaceMapOfEq, eqToHom_refl, Category.comp_id, mappingSpaceMap_fst]

theorem mappingSpaceVerticesEquiv_mapOfEq {Q Q' : SSet.{u}} (g : Q ⟶ Q')
    {a b : Q _⦋0⦌} {a' b' : Q' _⦋0⦌} (ha : g.app _ a = a') (hb : g.app _ b = b')
    (v : (mappingSpace Q a b) _⦋0⦌) :
    (mappingSpaceVerticesEquiv Q' a' b' ((mappingSpaceMapOfEq g ha hb).app _ v)).edge =
      g.app _ (mappingSpaceVerticesEquiv Q a b v).edge := by
  subst ha hb
  exact congrArg Edge.edge (mappingSpaceVerticesEquiv_map g a b v)

end SSet

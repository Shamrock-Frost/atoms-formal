import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpace
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed CartesianMonoidalCategory

universe u

namespace SSet

section Squares

variable {X : SSet.{u}} {x y : X _⦋0⦌}

private lemma side_uncurry_fst {Z : SSet.{u}} (g : Z ⟶ mappingSpace X x y) :
    lift (stdSimplex.isTerminalObj₀.from Z ≫ stdSimplex.δ 1) (𝟙 Z) ≫
        uncurry (g ≫ pullback.fst _ _) = stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm x ∧
      lift (stdSimplex.isTerminalObj₀.from Z ≫ stdSimplex.δ 0) (𝟙 Z) ≫
        uncurry (g ≫ pullback.fst _ _) = stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm y := by
  have h₀ := mappingSpace_fst_evalVertex_zero X x y
  have h₁ := mappingSpace_fst_evalVertex_one X x y
  have ht : g ≫ pullback.snd _ _ = stdSimplex.isTerminalObj₀.from Z :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [stdSimplex_δ_one_eq, stdSimplex_δ_zero_eq, ← comp_evalVertex, ← comp_evalVertex]
  exact ⟨(Category.assoc _ _ _).trans ((congrArg (g ≫ ·) h₀).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yonedaEquiv.symm x) ht))),
    (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) h₁).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yonedaEquiv.symm y) ht)))⟩

private lemma exists_mappingSpace_of_sides {Z : SSet.{u}} (G : Δ[1] ⊗ Z ⟶ X)
    (h₀ : lift (stdSimplex.isTerminalObj₀.from Z ≫ stdSimplex.δ 1) (𝟙 Z) ≫ G =
      stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm x)
    (h₁ : lift (stdSimplex.isTerminalObj₀.from Z ≫ stdSimplex.δ 0) (𝟙 Z) ≫ G =
      stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm y) :
    ∃ g : Z ⟶ mappingSpace X x y, g ≫ pullback.fst _ _ = curry G := by
  refine ⟨pullback.lift (curry G) (stdSimplex.isTerminalObj₀.from Z) ?_,
    pullback.lift_fst _ _ _⟩
  rw [stdSimplex_δ_one_eq] at h₀
  rw [stdSimplex_δ_zero_eq] at h₁
  ext1
  · rw [Category.assoc, ihomStdSimplexOneEval, lift_fst, Category.assoc, lift_fst,
      comp_evalVertex, uncurry_curry, h₀]
  · rw [Category.assoc, ihomStdSimplexOneEval, lift_snd, Category.assoc, lift_snd,
      comp_evalVertex, uncurry_curry, h₁]

private lemma mappingSpaceVerticesEquiv_δ_edge (s : (mappingSpace X x y) _⦋1⦌) (i : Fin 2) :
    (mappingSpaceVerticesEquiv X x y ((mappingSpace X x y).δ i s)).edge =
      yonedaEquiv (lift (𝟙 Δ[1]) (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ i) ≫
        uncurry (yonedaEquiv.symm s ≫ pullback.fst _ _)) := by
  rw [mappingSpaceVerticesEquiv_edge, ← stdSimplex.δ_comp_yonedaEquiv_symm]
  refine congrArg yonedaEquiv ((congrArg (fun k ↦ lift (𝟙 Δ[1])
    (stdSimplex.isTerminalObj₀.from Δ[1]) ≫ uncurry k) (Category.assoc _ _ _)).trans ?_)
  rw [uncurry_natural_left, lift_whiskerLeft_assoc]

end Squares

section Shapes

private lemma stdSimplex_hom_ext {m n : ℕ} {f g : (Δ[m] : SSet.{u}) ⟶ Δ[n]}
    (h : ∀ i, yonedaEquiv f i = yonedaEquiv g i) : f = g :=
  yonedaEquiv.injective (stdSimplex.ext _ _ h)

private lemma stdSimplex_square_hom_ext {m : ℕ} {f g : (Δ[m] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]}
    (h₁ : ∀ i, yonedaEquiv (f ≫ fst _ _) i = yonedaEquiv (g ≫ fst _ _) i)
    (h₂ : ∀ i, yonedaEquiv (f ≫ snd _ _) i = yonedaEquiv (g ≫ snd _ _) i) : f = g := by
  ext1
  · exact stdSimplex_hom_ext h₁
  · exact stdSimplex_hom_ext h₂

private lemma δ_diagonal :
    stdSimplex.δ 1 ≫ lift (𝟙 Δ[1]) (𝟙 Δ[1]) = stdSimplex.δ 1 ≫
        lift (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 1) (𝟙 (Δ[1] : SSet.{u})) ∧
      stdSimplex.δ 0 ≫ lift (𝟙 Δ[1]) (𝟙 Δ[1]) = stdSimplex.δ 0 ≫
        lift (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 0) (𝟙 (Δ[1] : SSet.{u})) :=
  ⟨stdSimplex_square_hom_ext (by decide) (by decide),
    stdSimplex_square_hom_ext (by decide) (by decide)⟩

private def squareCollapse : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.1 = 0 then 0 else if p.2 = 0 then 1 else 2
  monotone' := by decide

private def squareToTriangle : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[2] where
  app _ := ↾fun s ↦ stdSimplex.objMk (squareCollapse.comp
    ((stdSimplex.asOrderHom s.1).prod (stdSimplex.asOrderHom s.2)))
  naturality _ _ _ := rfl

private lemma squareToTriangle_sides :
    lift (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 1) (𝟙 Δ[1]) ≫
        squareToTriangle.{u} =
          stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 1 ≫ stdSimplex.δ 2 ∧
      lift (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 0) (𝟙 Δ[1]) ≫
        squareToTriangle.{u} = stdSimplex.δ 0 ∧
      lift (𝟙 Δ[1]) (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 1) ≫
        squareToTriangle.{u} = stdSimplex.δ 2 ∧
      lift (𝟙 Δ[1]) (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 0) ≫
        squareToTriangle.{u} = stdSimplex.δ 1 :=
  ⟨stdSimplex_hom_ext (by decide), stdSimplex_hom_ext (by decide),
    stdSimplex_hom_ext (by decide), stdSimplex_hom_ext (by decide)⟩

end Shapes

section PiZero

variable {X : SSet.{u}} {x y : X _⦋0⦌}

private def edgeOfHom (h : Δ[1] ⟶ X) (h₀ : stdSimplex.δ 1 ≫ h = yonedaEquiv.symm x)
    (h₁ : stdSimplex.δ 0 ≫ h = yonedaEquiv.symm y) : Edge x y :=
  Edge.mk (yonedaEquiv h)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, h₀, Equiv.apply_symm_apply])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, h₁, Equiv.apply_symm_apply])

private lemma yonedaEquiv_const_eq (z : X _⦋0⦌) :
    yonedaEquiv (stdSimplex.isTerminalObj₀.from Δ[1] ≫ yonedaEquiv.symm z) = (Edge.id z).edge := by
  rw [← stdSimplex.isTerminalObj₀.hom_ext (stdSimplex.σ 0) (stdSimplex.isTerminalObj₀.from _),
    stdSimplex.σ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply, Edge.id_edge]

private lemma homMk_δ_eq (s : (mappingSpace X x y) _⦋1⦌) :
    Truncated.HomotopyCategory.homMk
        (mappingSpaceVerticesEquiv X x y ((mappingSpace X x y).δ 1 s)).toTruncated =
      Truncated.HomotopyCategory.homMk
        (mappingSpaceVerticesEquiv X x y ((mappingSpace X x y).δ 0 s)).toTruncated := by
  let S : Δ[1] ⊗ Δ[1] ⟶ X := uncurry (yonedaEquiv.symm s ≫ pullback.fst _ _)
  obtain ⟨hx, hy⟩ := side_uncurry_fst (yonedaEquiv.symm s)
  have ht₀ : stdSimplex.δ 1 ≫ stdSimplex.isTerminalObj₀.from Δ[1] = 𝟙 _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  have ht₁ : stdSimplex.δ 0 ≫ stdSimplex.isTerminalObj₀.from Δ[1] = 𝟙 _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  let d : Edge x y := edgeOfHom (lift (𝟙 Δ[1]) (𝟙 Δ[1]) ≫ S)
    (by rw [← Category.assoc, δ_diagonal.1, Category.assoc, hx, ← Category.assoc, ht₀,
      Category.id_comp])
    (by rw [← Category.assoc, δ_diagonal.2, Category.assoc, hy, ← Category.assoc, ht₁,
      Category.id_comp])
  have hc₀ : stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0) =
      stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 1 := stdSimplex_hom_ext.{u} (by decide)
  have hc₁ : stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1) =
      stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 0 := stdSimplex_hom_ext.{u} (by decide)
  have cu : Edge.CompStruct (Edge.id x)
      (mappingSpaceVerticesEquiv X x y ((mappingSpace X x y).δ 0 s)) d :=
    Edge.CompStruct.mk (yonedaEquiv (prodStdSimplex.upperTriangle ≫ S))
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_two_upperTriangle, hc₀, hx, yonedaEquiv_const_eq])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_zero_upperTriangle, hc₁, mappingSpaceVerticesEquiv_δ_edge])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_one_upperTriangle]; rfl)
  have cl : Edge.CompStruct
      (mappingSpaceVerticesEquiv X x y ((mappingSpace X x y).δ 1 s))
      (Edge.id y) d :=
    Edge.CompStruct.mk (yonedaEquiv (prodStdSimplex.lowerTriangle ≫ S))
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_two_lowerTriangle, hc₀, mappingSpaceVerticesEquiv_δ_edge])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_zero_lowerTriangle, hc₁, hy, yonedaEquiv_const_eq])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_one_lowerTriangle]; rfl)
  have hcu := Truncated.HomotopyCategory.homMk_comp_homMk cu.toTruncated
  have hcl := Truncated.HomotopyCategory.homMk_comp_homMk cl.toTruncated
  exact (Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
    (Truncated.HomotopyCategory.homMk_id _).symm).trans (hcl.trans (hcu.symm.trans
      ((congrArg (· ≫ _) (Truncated.HomotopyCategory.homMk_id _)).trans (Category.id_comp _)))))

private lemma π₀_mk_eq_of_compStruct {v w : (mappingSpace X x y) _⦋0⦌}
    (t : Edge.CompStruct (mappingSpaceVerticesEquiv X x y v) (Edge.id y)
      (mappingSpaceVerticesEquiv X x y w)) :
    π₀.mk v = π₀.mk w := by
  obtain ⟨hc₀, hc₁, hc₂, hc₃⟩ := squareToTriangle_sides.{u}
  let S : Δ[1] ⊗ Δ[1] ⟶ X := squareToTriangle ≫ yonedaEquiv.symm t.simplex
  obtain ⟨G, hG⟩ := exists_mappingSpace_of_sides S
    (by rw [← Category.assoc, hc₀, Category.assoc, Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, t.d₂, Edge.src_eq])
    (by rw [← Category.assoc, hc₁, stdSimplex.δ_comp_yonedaEquiv_symm, t.d₀, Edge.id_edge,
      ← stdSimplex.σ_comp_yonedaEquiv_symm,
      stdSimplex.isTerminalObj₀.hom_ext (stdSimplex.σ 0) (stdSimplex.isTerminalObj₀.from _)])
  have hv : (mappingSpace X x y).δ 1 (yonedaEquiv G) = v :=
    (mappingSpaceVerticesEquiv X x y).injective (Edge.ext (by
      rw [mappingSpaceVerticesEquiv_δ_edge, Equiv.symm_apply_apply, hG, uncurry_curry,
        ← Category.assoc, hc₂,
        stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply, t.d₂]))
  have hw : (mappingSpace X x y).δ 0 (yonedaEquiv G) = w :=
    (mappingSpaceVerticesEquiv X x y).injective (Edge.ext (by
      rw [mappingSpaceVerticesEquiv_δ_edge, Equiv.symm_apply_apply, hG, uncurry_curry,
        ← Category.assoc, hc₃,
        stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply, t.d₁]))
  rw [← hv, ← hw]
  exact π₀.sound (Edge.mk' (yonedaEquiv G))

noncomputable def π₀MappingSpaceEquiv (X : SSet.{u}) [X.Quasicategory] (x y : X _⦋0⦌) :
    π₀ (mappingSpace X x y) ≃
      (Truncated.HomotopyCategory.mk (V := (truncation 2).obj X) x ⟶
        Truncated.HomotopyCategory.mk y) :=
  Equiv.ofBijective
    (π₀.lift (fun v ↦ Truncated.HomotopyCategory.homMk
      (mappingSpaceVerticesEquiv X x y v).toTruncated) fun v w e ↦ by
        have h := homMk_δ_eq e.edge
        rwa [e.src_eq, e.tgt_eq] at h) (by
    refine ⟨fun c c' h ↦ ?_, fun φ ↦ ?_⟩
    · obtain ⟨v, rfl⟩ := π₀.mk_surjective c
      obtain ⟨w, rfl⟩ := π₀.mk_surjective c'
      rw [π₀.lift_mk, π₀.lift_mk] at h
      exact π₀_mk_eq_of_compStruct (Edge.CompStruct.ofTruncated
        ((Truncated.HomotopyCategory.homMk_eq_homMk_iff _ _).1 h).some)
    · obtain ⟨e, rfl⟩ := Truncated.HomotopyCategory.homMk_surjective φ
      exact ⟨π₀.mk ((mappingSpaceVerticesEquiv X x y).symm (Edge.ofTruncated e)), by
        rw [π₀.lift_mk, Equiv.apply_symm_apply]
        rfl⟩)

theorem π₀MappingSpaceEquiv_mk (X : SSet.{u}) [X.Quasicategory] (x y : X _⦋0⦌)
    (v : (mappingSpace X x y) _⦋0⦌) :
    π₀MappingSpaceEquiv X x y (π₀.mk v) =
      Truncated.HomotopyCategory.homMk (mappingSpaceVerticesEquiv X x y v).toTruncated :=
  rfl

end PiZero

section Arrows

variable {X : SSet.{u}}

noncomputable def ihomStdSimplexOneEdge (v : ((ihom Δ[1]).obj X) _⦋0⦌) : X _⦋1⦌ :=
  yonedaEquiv (ihomPointEquiv Δ[1] X (yonedaEquiv.symm v))

lemma δ_one_ihomStdSimplexOneEdge (v : ((ihom Δ[1]).obj X) _⦋0⦌) :
    X.δ 1 (ihomStdSimplexOneEdge v) = (evalVertex (stdSimplex.obj₀Equiv.symm 0) X).app _ v := by
  rw [ihomStdSimplexOneEdge, ← stdSimplex.yonedaEquiv_δ_comp, stdSimplex_δ_one_eq,
    ← comp_evalVertex_eq, yonedaEquiv_comp, Equiv.apply_symm_apply]

lemma δ_zero_ihomStdSimplexOneEdge (v : ((ihom Δ[1]).obj X) _⦋0⦌) :
    X.δ 0 (ihomStdSimplexOneEdge v) = (evalVertex (stdSimplex.obj₀Equiv.symm 1) X).app _ v := by
  rw [ihomStdSimplexOneEdge, ← stdSimplex.yonedaEquiv_δ_comp, stdSimplex_δ_zero_eq,
    ← comp_evalVertex_eq, yonedaEquiv_comp, Equiv.apply_symm_apply]

theorem homMk_comp_homMk_of_edge_ihomStdSimplexOne {u u' : ((ihom Δ[1]).obj X) _⦋0⦌}
    (E : Edge u u') {a b a' b' : X _⦋0⦌} {f : Edge a b} {f' : Edge a' b'} {p : Edge a a'}
    {q : Edge b b'} (hf : f.edge = ihomStdSimplexOneEdge u)
    (hf' : f'.edge = ihomStdSimplexOneEdge u')
    (hp : p.edge = (evalVertex (stdSimplex.obj₀Equiv.symm 0) X).app _ E.edge)
    (hq : q.edge = (evalVertex (stdSimplex.obj₀Equiv.symm 1) X).app _ E.edge) :
    Truncated.HomotopyCategory.homMk (V := (truncation 2).obj X) f.toTruncated ≫
        Truncated.HomotopyCategory.homMk q.toTruncated =
      Truncated.HomotopyCategory.homMk p.toTruncated ≫
        Truncated.HomotopyCategory.homMk f'.toTruncated := by
  let S : Δ[1] ⊗ Δ[1] ⟶ X := uncurry (yonedaEquiv.symm E.edge)
  have hS (i : Fin 2) : yonedaEquiv (lift (𝟙 Δ[1])
      (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ i) ≫ S) =
        ihomStdSimplexOneEdge (((ihom Δ[1]).obj X).δ i E.edge) := by
    rw [ihomStdSimplexOneEdge, ihomPointEquiv_apply, ← stdSimplex.δ_comp_yonedaEquiv_symm,
      uncurry_natural_left, lift_whiskerLeft_assoc]
  have hS₀ : yonedaEquiv (lift (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 1)
      (𝟙 Δ[1]) ≫ S) = p.edge := by
    rw [hp, stdSimplex_δ_one_eq, ← comp_evalVertex, yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hS₁ : yonedaEquiv (lift (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 0)
      (𝟙 Δ[1]) ≫ S) = q.edge := by
    rw [hq, stdSimplex_δ_zero_eq, ← comp_evalVertex, yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hc₀ : stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0) =
      stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 1 := stdSimplex_hom_ext.{u} (by decide)
  have hc₁ : stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1) =
      stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ 0 := stdSimplex_hom_ext.{u} (by decide)
  let d : Edge a b' := Edge.mk (yonedaEquiv (lift (𝟙 Δ[1]) (𝟙 Δ[1]) ≫ S))
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, δ_diagonal.1, Category.assoc,
      stdSimplex.yonedaEquiv_δ_comp, hS₀, p.src_eq])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, δ_diagonal.2, Category.assoc,
      stdSimplex.yonedaEquiv_δ_comp, hS₁, q.tgt_eq])
  have cl : Edge.CompStruct f q d :=
    Edge.CompStruct.mk (yonedaEquiv (prodStdSimplex.lowerTriangle ≫ S))
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_two_lowerTriangle, hc₀, hS, E.src_eq, hf])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_zero_lowerTriangle, hc₁, hS₁])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_one_lowerTriangle]; rfl)
  have cu : Edge.CompStruct p f' d :=
    Edge.CompStruct.mk (yonedaEquiv (prodStdSimplex.upperTriangle ≫ S))
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_two_upperTriangle, hc₀, hS₀])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_zero_upperTriangle, hc₁, hS, E.tgt_eq, hf'])
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        prodStdSimplex.δ_one_upperTriangle]; rfl)
  exact (Truncated.HomotopyCategory.homMk_comp_homMk cl.toTruncated).trans
    (Truncated.HomotopyCategory.homMk_comp_homMk cu.toTruncated).symm

end Arrows

end SSet

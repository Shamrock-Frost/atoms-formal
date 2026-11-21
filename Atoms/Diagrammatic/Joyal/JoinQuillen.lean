import Atoms.Diagrammatic.Joyal.JoinWalkingEquivalence
import Atoms.Diagrammatic.Joyal.SourceHornFibration
import Atoms.Diagrammatic.SliceLifting
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Over
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen

open CategoryTheory CategoryTheory.WithInitial Limits MorphismProperty HomotopicalAlgebra
  Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open scoped DiagSet.Join

private theorem hasLiftingProperty_of_toInfty_one {A B X Y : DiagSet.{u}} {i : A ⟶ B}
    {p : X ⟶ Y} (hi : trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map i))
    [hp : Fibration ((DiagSet.toInfty 1).map p)] : HasLiftingProperty i p :=
  (hp.mem : reversibleCylinder.{u}.fibrations (inftyGenerators 1) p) _ hi

private theorem fibration_toInfty_one_pullback_snd {A B C : DiagSet.{u}} (f : A ⟶ C) (g : B ⟶ C)
    [hf : Fibration ((DiagSet.toInfty 1).map f)] :
    Fibration ((DiagSet.toInfty 1).map (pullback.snd f g)) :=
  (fibration_iff _).2 ((fibrations (DiagSet.Infty.{u} 1)).of_isPullback
    (IsPullback.of_hasPullback f g) ((fibration_iff _).1 hf))

theorem isFibrant_slice_of_isFibrant {T X : DiagSet.{u}}
    [hX : IsFibrant ((DiagSet.toInfty 1).obj X)] (t : T ⟶ X) :
    IsFibrant ((DiagSet.toInfty 1).obj ((WithInitial.slice T).obj (Under.mk t))) := by
  have hX' := (isInftyCategory_iff_rlp 1 X).1 ((isFibrant_infty_iff 1 X).1 hX)
  have hp : Fibration ((DiagSet.toInfty 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 hX
  have hl : (inftyGenerators.{u} 1).rlp (leibnizSlice (initial.to T) (terminal.from X) t) :=
    fun A B g hg ↦ (hasLiftingProperty_pushoutObjObj_ι_iff _ _).1
      (hasLiftingProperty_of_toInfty_one
        (trivialCofibration_toInfty_pushoutObjObj_ι_of_saturation_inftyGenerators
          (le_saturation _ _ hg) (initial.to T)) (hp := hp)) t
  have hg : (inftyGenerators.{u} 1).rlp
      ((sliceRes (initial.to T)).app (Under.mk (t ≫ terminal.from X))) := by
    have := isIso_of_isTerminal (isTerminalSliceObj _ terminalIsTerminal)
      (isTerminalSliceObj _ terminalIsTerminal)
      ((sliceRes (initial.to T)).app (Under.mk (t ≫ terminal.from X)))
    exact rlp_of_isIso _ _
  have hfst := MorphismProperty.pullback_fst ((slice (⊥_ DiagSet.{u})).map
    (Under.homMk (terminal.from X) (by simp) :
      Under.mk (initial.to T ≫ t) ⟶ Under.mk (initial.to T ≫ t ≫ terminal.from X))) _ hg
  have hiso := rlp_of_isIso (inftyGenerators.{u} 1)
    (sliceEmptyIso initialIsInitial ((Under.map (initial.to T)).obj (Under.mk t))).hom
  have h : (inftyGenerators.{u} 1).rlp (terminal.from ((slice T).obj (Under.mk t))) := by
    rw [terminal.hom_ext (terminal.from _) (leibnizSlice (initial.to T) (terminal.from X) t ≫
      pullback.fst _ _ ≫ (sliceEmptyIso initialIsInitial
        ((Under.map (initial.to T)).obj (Under.mk t))).hom ≫ terminal.from X)]
    exact comp_mem _ _ _ hl (comp_mem _ _ _ hfst (comp_mem _ _ _ hiso hX'))
  exact (isFibrant_infty_iff 1 _).2 ((isInftyCategory_iff_rlp 1 _).2 h)

private theorem fibration_leibnizSlice_of_fibration_slice_map {S T X Y : DiagSet.{u}}
    (j : S ⟶ T) [Mono j] {p : X ⟶ Y} [hX : IsFibrant ((DiagSet.toInfty 1).obj X)]
    [hY : IsFibrant ((DiagSet.toInfty 1).obj Y)] [hp : Fibration ((DiagSet.toInfty 1).map p)]
    (t : T ⟶ X)
    [hS : Fibration ((DiagSet.toInfty 1).map ((slice S).map (Under.homMk p (by simp) :
      Under.mk (j ≫ t) ⟶ Under.mk (j ≫ t ≫ p))))] :
    Fibration ((DiagSet.toInfty 1).map (leibnizSlice j p t)) := by
  refine fibration_toInfty_one_of_rlp_sourceHorns _
    (hX := isFibrant_slice_of_isFibrant (hX := hX) t) (hY := ?_)
    fun A B g hg ↦ (hasLiftingProperty_pushoutObjObj_ι_iff _ _).1
      (hasLiftingProperty_of_toInfty_one
        (trivialCofibration_toInfty_pushoutObjObj_ι_of_saturation_sourceHorns
          (le_saturation _ _ hg) j) (hp := hp)) t
  have h₁ := fibration_toInfty_one_pullback_snd _ ((sliceRes j).app (Under.mk (t ≫ p))) (hf := hS)
  have h₂ := isFibrant_slice_of_isFibrant (hX := hY) (t ≫ p)
  exact @isFibrant_of_fibration _ _ _ _ _ _ _ _ h₁ h₂

private theorem fibration_slice_initial_map {X Y : Under (⊥_ DiagSet.{u})} (φ : X ⟶ Y)
    [hp : Fibration ((DiagSet.toInfty 1).map φ.right)] :
    Fibration ((DiagSet.toInfty 1).map ((slice (⊥_ DiagSet.{u})).map φ)) := by
  refine (fibration_iff _).2 (((fibrations (DiagSet.Infty.{u} 1)).arrow_mk_iso_iff
    (Arrow.isoMk (sliceEmptyIso initialIsInitial X) (sliceEmptyIso initialIsInitial Y) ?_)).2
      ((fibration_iff _).1 hp))
  exact ((sliceProj (⊥_ DiagSet.{u})).naturality φ).symm

private theorem fibration_slice_map_homMk {S X Y : DiagSet.{u}} {p : X ⟶ Y}
    [hX : IsFibrant ((DiagSet.toInfty 1).obj X)] [hY : IsFibrant ((DiagSet.toInfty 1).obj Y)]
    [hp : Fibration ((DiagSet.toInfty 1).map p)] (s : S ⟶ X) (s' : S ⟶ Y) (h : s ≫ p = s') :
    Fibration ((DiagSet.toInfty 1).map ((slice S).map
      (Under.homMk p h : Under.mk s ⟶ Under.mk s'))) := by
  subst h
  have hl := fibration_leibnizSlice_of_fibration_slice_map (initial.to S) (hX := hX) (hY := hY)
    (hp := hp) s (hS := fibration_slice_initial_map _ (hp := hp))
  have := fibration_toInfty_one_pullback_snd ((slice (⊥_ DiagSet.{u})).map
      (Under.homMk p (by simp) : Under.mk (initial.to S ≫ s) ⟶
        Under.mk (initial.to S ≫ s ≫ p)))
    ((sliceRes (initial.to S)).app (Under.mk (s ≫ p)))
    (hf := fibration_slice_initial_map _ (hp := hp))
  rw [← leibnizSlice_snd (initial.to S) p s, Functor.map_comp]
  infer_instance

private theorem fibration_slice_map {T : DiagSet.{u}} {X Y : Under T} (p : X ⟶ Y)
    [hX : IsFibrant ((DiagSet.toInfty 1).obj X.right)]
    [hY : IsFibrant ((DiagSet.toInfty 1).obj Y.right)]
    [hp : Fibration ((DiagSet.toInfty 1).map p.right)] :
    Fibration ((DiagSet.toInfty 1).map ((slice T).map p)) := by
  obtain ⟨X, x, rfl⟩ := Under.mk_surjective X
  obtain ⟨Y, y, rfl⟩ := Under.mk_surjective Y
  obtain ⟨q, hq, rfl⟩ := Under.homMk_surjective p
  exact fibration_slice_map_homMk (hX := hX) (hY := hY) (hp := hp) x y hq

noncomputable def joinRightUnderInfty (T : DiagSet.{u}) :
    DiagSet.Infty.{u} 1 ⥤ Under ((DiagSet.toInfty 1).obj T) :=
  WithInitial.joinRightUnder T

noncomputable def sliceInfty (T : DiagSet.{u}) :
    Under ((DiagSet.toInfty 1).obj T) ⥤ DiagSet.Infty.{u} 1 :=
  WithInitial.slice T

noncomputable def joinRightUnderAdjunctionInfty (T : DiagSet.{u}) :
    joinRightUnderInfty T ⊣ sliceInfty T :=
  WithInitial.joinRightUnderAdjunction T

theorem isQuillen_joinRightUnder (T : DiagSet.{u}) :
    (joinRightUnderAdjunctionInfty T).IsQuillen := by
  refine (joinRightUnderAdjunctionInfty T).isQuillen_of_fibrations_between_fibrant
    (fun _ _ g hg ↦ ?_) fun X Y p hX hY hp ↦ fibration_slice_map p
      (hX := (isFibrant_under_iff _ X).1 hX) (hY := (isFibrant_under_iff _ Y).1 hY)
      (hp := (fibrations_under_iff _ p).1 hp)
  exact (cofibration_iff _).1 ((cofibrations_under_iff _ _).2 ((cofibration_iff _).2
    (@mono_joinMap _ _ _ _ g (𝟙 T) hg _)))

theorem trivialCofibration_toInfty_of_anodyne {n : ℕ∞} {A B : DiagSet.{u}} {g : A ⟶ B}
    (hg : reversibleCylinder.{u}.anodyne (inftyGenerators n) g) :
    trivialCofibrations (DiagSet.Infty.{u} n) ((DiagSet.toInfty n).map g) :=
  have hS := inftyGenerators_le_monomorphisms.{u} n
  (⟨reversibleCylinder.{u}.anodyne_le_monomorphisms _ hS g hg,
    reversibleCylinder.{u}.anodyne_le_weakEquivalences (S := inftyGenerators n) hS g hg⟩ :
      reversibleCylinder.{u}.trivialCofibrations (inftyGenerators n) g)

theorem trivialCofibration_toInfty_joinMap_id {A B : DiagSet.{u}} {g : A ⟶ B}
    (hg : trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map g))
    (T : DiagSet.{u}) :
    trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map (joinMap g (𝟙 T))) :=
  (isQuillen_joinRightUnder T).trivialCofibrations_le _ hg

theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_trivialCofibration {A B S T : DiagSet.{u}}
    {g : A ⟶ B} (hg : trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map g))
    (j : S ⟶ T) [Mono j] :
    trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 g j).ι) := by
  have : Mono g := ((mem_trivialCofibrations_iff _).1 hg).1.mem
  have hinr : trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 g j).inr) :=
    (trivialCofibrations (DiagSet.Infty.{u} 1)).of_isPushout
    (Functor.PushoutObjObj.ofHasPushout 𝒥 g j).isPushout.flip
    (trivialCofibration_toInfty_joinMap_id hg S)
  have := ((mem_trivialCofibrations_iff _).1 hinr).2
  have : WeakEquivalence ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 g j).inr ≫
      (DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 g j).ι) := by
    rw [← Functor.map_comp, (Functor.PushoutObjObj.ofHasPushout 𝒥 g j).inr_ι]
    exact ((mem_trivialCofibrations_iff _).1 (trivialCofibration_toInfty_joinMap_id hg T)).2
  refine (mem_trivialCofibrations_iff _).2 ⟨(cofibration_iff _).2 ?_,
    weakEquivalence_of_precomp_of_fac (f := (DiagSet.toInfty 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 g j).inr) rfl⟩
  exact mono_pushoutObjObj_ι_join g j

theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_anodyne_of_mono {A B S T : DiagSet.{u}}
    {g : A ⟶ B} (hg : reversibleCylinder.{u}.anodyne (inftyGenerators 1) g) (j : S ⟶ T)
    [Mono j] :
    trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 g j).ι) :=
  trivialCofibration_toInfty_pushoutObjObj_ι_of_trivialCofibration
    (trivialCofibration_toInfty_of_anodyne hg) j

theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_anodyneGenerators ⦃A B : DiagSet.{u}⦄
    (g : A ⟶ B) (hg : reversibleCylinder.{u}.anodyneGenerators (inftyGenerators 1) g)
    (V : Atom) :
    trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (WithInitial.joinFunctor (C := Atom) : DiagSet × DiagSet ⥤ DiagSet))
        g (sphereInclusion.{u} V)).ι) := by
  refine trivialCofibration_toInfty_pushoutObjObj_ι_of_anodyne_of_mono ?_ (sphereInclusion V)
  rw [reversibleCylinder.{u}.anodyne_eq_saturation_anodyneGenerators _
    (inftyGenerators_le_monomorphisms.{u} 1)]
  exact le_saturation _ _ hg

theorem fibration_leibnizSlice {S T X Y : DiagSet.{u}} (j : S ⟶ T) [Mono j] {p : X ⟶ Y}
    [hp : Fibration ((DiagSet.toInfty 1).map p)] (t : T ⟶ X) :
    Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizSlice j p t)) := by
  rw [fibration_iff, ← trivialCofibrations_rlp]
  intro K L i hi
  exact (hasLiftingProperty_pushoutObjObj_ι_iff _ p).1 (hasLiftingProperty_of_toInfty_one
    (trivialCofibration_toInfty_pushoutObjObj_ι_of_trivialCofibration (g := i) hi j) (hp := hp)) t

theorem weakEquivalence_joinMap_id {X X' : DiagSet.{u}} (f : X ⟶ X') (T : DiagSet.{u})
    [hf : WeakEquivalence ((DiagSet.toInfty 1).map f)] :
    WeakEquivalence ((DiagSet.toInfty 1).map (joinMap f (𝟙 T))) := by
  exact (weakEquivalences_under_iff _ _).1
    ((isQuillen_joinRightUnder T).weakEquivalence_map ((DiagSet.toInfty 1).map f))

end Atoms.Diagrammatic

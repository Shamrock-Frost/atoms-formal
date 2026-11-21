import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

namespace CategoryTheory.Limits.Types

open Opposite

universe u

variable (ι : Type u)

def sigmaFunctor : (Discrete ι ⥤ Type u) ⥤ Type u where
  obj P := Σ i : ι, P.obj ⟨i⟩
  map {P Q} φ := TypeCat.ofHom fun p : Σ i : ι, P.obj ⟨i⟩ =>
    (⟨p.1, φ.app ⟨p.1⟩ p.2⟩ : Σ i : ι, Q.obj ⟨i⟩)

def sigmaConstAdj : sigmaFunctor ι ⊣ Functor.const (Discrete ι) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P T =>
        { toFun := fun h => Discrete.natTrans fun i =>
            TypeCat.ofHom fun p => h (⟨i.as, p⟩ : Σ i : ι, P.obj ⟨i⟩)
          invFun := fun φ => TypeCat.ofHom fun p : Σ i : ι, P.obj ⟨i⟩ => φ.app ⟨p.1⟩ p.2
          left_inv := fun _ => rfl
          right_inv := fun _ => by ext; rfl }
      homEquiv_naturality_left_symm := fun _ _ => rfl }

instance preservesColimitsOfSize_sigmaFunctor :
    PreservesColimitsOfSize.{u, u} (sigmaFunctor ι) :=
  (sigmaConstAdj ι).leftAdjoint_preservesColimits

def sigmaEvaluation (A : Type u) [SmallCategory A] {ι : Type u} (f : ι → A) :
    (Aᵒᵖ ⥤ Type u) ⥤ Type u :=
  (Functor.whiskeringLeft (Discrete ι) Aᵒᵖ (Type u)).obj (Discrete.functor fun i => op (f i)) ⋙
    sigmaFunctor ι

instance preservesColimitsOfSize_sigmaEvaluation (A : Type u) [SmallCategory A] {ι : Type u}
    (f : ι → A) : PreservesColimitsOfSize.{u, u} (sigmaEvaluation A f) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    ((Functor.whiskeringLeft (Discrete ι) Aᵒᵖ (Type u)).obj (Discrete.functor fun i => op (f i)) ⋙
      sigmaFunctor ι))

end CategoryTheory.Limits.Types

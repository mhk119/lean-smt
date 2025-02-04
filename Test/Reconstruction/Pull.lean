import Smt

open Smt.Reconstruction.Certifying

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G → A ∨ B ∨ C ∨ F ∨ D ∨ E ∨ G := by
  intro h
  pullToMiddle 3, 5, h, h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H ∨ I ∨ J →
          A ∨ J ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H ∨ I := by
  intro h
  pullToMiddle 1, 9, h, h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → A ∨ B ∨ C ∨ G ∨ D ∨ E ∨ F ∨ H := by
  intro h
  pullToMiddle 3, 6, h, h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → A ∨ B ∨ E ∨ C ∨ D ∨ F ∨ G ∨ H := by
  intro h
  pullToMiddle 2, 4, h, h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → E ∨ A ∨ B ∨ C ∨ D ∨ F ∨ G ∨ H := by
  intro h
  pullToMiddle 0, 4, h, h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → A ∨ G ∨ B ∨ C ∨ D ∨ E ∨ F ∨ H := by
  intro h
  pullToMiddle 1, 6, h, h₂

example : A ∨ B ∨ C ∨ D ∨ E ∨ F → A ∨ B ∨ C ∨ F ∨ D ∨ E := by
  intro h
  pullToMiddle 3, 5, h, h₂

example : A ∨ B ∨ C ∨ D ∨ E → A ∨ E ∨ B ∨ C ∨ D := by
  intro h
  pullToMiddle 1, 4, h, h₂

example : A ∨ B ∨ C ∨ D ∨ E → (D ∨ E) ∨ A ∨ B ∨ C := by
  intro h
  pull h, (D ∨ E),  3

example : A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H → F ∨ A ∨ B ∨ C ∨ D ∨ E ∨ G ∨ H := by
  intro h
  pull h, F


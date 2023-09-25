/-!
# Team Projects
This file describes the projects of each team.

## General Requirement

1. Each team should have a team leader. The `team leader` upload the finished project by creating a github pull request, with pull request name in the following format `Team_n_project_changed_xxx.lean_and_yyy.lean`, where n is your team number, xxx.lean is the file you edited.

2. Without a discussion with Jiang Jiedong, you should only fill in sorry's (or delete "by" if you want) and NOT change any other place. You are allowed (and encouraged) to use theorems whose proof is still a sorry in your proof, as long as the file imports this theorem or the theorem is in the same file. If you discover errors in statements or have ideas on formulating new theorems, please feel free to contact Jiang Jiedong.

3. Please write you code in a clean and readable way. You are encouraged to read other files and imitating them. This is necessary for you to understand the definitions. And please note that we will have more requirements on writing inline comments in future.

4. Currently, the whole design of this Euclidean Geometry project is still unstable, even for the very foundation files. It is possible to reformulate and reprove many currently existing theorems under the new design. As a result, building your proof dependent on fancier, later theorems is much better than building your proof on very elemental theorems (such as unfold everything). This is so called `de-couple`. It minimize the effort of implementing new designs, changing one place will not raise errors everywhere. We kindly ask you to follow this principle.

## Project Detail
Team D 1 Muqing Jiang : 
* Fills sorry's in Plane.lean, section length, and section existence in Ray.lean.
* Formalize ShanZun Exercise_1a 1b (1.3-1.6)

Team A 2 Yongle Bai :
* Fills sorry's in section coersion_compatibility and section midpoint Ray.lean
`Team A cease to exist`

Team F 3 Zhuoni Chi :
* Fills sorry's in Ray_ex.lean `Finished` `Improved the proof greatly`
* Fills statements in Ray_ex2.lean `Finished`
* Fills proofs in Ray_ex2.lean
* Formalize ShanZun Exercise_1c 1d 1.7-1.10 `low priority for now`

Team C 4 Xintao Yu :
* Fills sorry's in Line.lean

Team E 5 Haoran Wang → Yuchen Xie :
* Fills sorry's in Line_ex.lean

Team H 6 Yebo Peng :
* Fills sorry's in Perpendicular.lean `Finished`
* Fills sorry's in cosine theorem and prove SAS in congreunce.lean 

Team G 7 Zhaohui Zong :
* Fills sorry's in Congruence.lean, but you may leave SAS blank and use SAS (and cosine theorem, sine theorem) to show other triangle congruence criteria.

Team B 8 Zhehao Zheng :
* Fills sorry's in IsocelesTriangle.lean
* Formalize ShanZun Exercise 1.1 1.2
* Formalize ArefWernick-Chap1 Chap1a
* Formalize AOPS Chap3a.lean


## Special Notes

* Vector.lean has been updated, please sync fork then pull to keep update.

* Line.lean and Line_ex.lean is under a major reform. Please wait for the update.
-/

/-!
## New Team Projects

0. Each team should continue to fill in sorry's of their own file. New theorems in early files are still increasing as formalizing advanced theorems creates more needs.

1. Finish Axiom/Linear
Jiedong Jiang, Yongle Hu + 1 Team G

2. Create Axiom/Circle 
Shun Yin + 1 Team E

3. Create Construction/AngleBisector 
Yuefeng Wang + 1 Team C

4. Rebuild Construction/Position (especially det, oriented area, theorems in Position.lean) 
Yibing Chen + 1 Team H

5. Formalize exercises 
Liang Xiao + 2 Team B F

6. Create Construction/PolygonParallelogram.lean
Jiedong Jiang + 1 Team D

## Special Missions

1. Finish sine theorem and related theorems. Assigned to Yebo Peng, after formalized oriented area.

2. Tactics. For those who are interested in writing tactics, we will arrange trainings by Anjie Dong. `TBA` 
-/
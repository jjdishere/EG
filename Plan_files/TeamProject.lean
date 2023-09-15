/-!
# Team Projects
This file describes the projects of each team.

## General Requirement

1. Each team should have a team leader. The `team leader` upload the finished project by creating a github pull request, with pull request name in the following format `Team_n_project_changed_xxx.lean_and_yyy.lean`, where n is your team number, xxx.lean is the file you edited.

2. Without a discussion with Jiang Jiedong, you should only fill in sorry's (or delete "by" if you want) and NOT change any other place. You are allowed (and encouraged) to use theorems whose proof is still a sorry in your proof, as long as the file imports this theorem or the theorem is in the same file. If you discover errors in statements or have ideas on formulating new theorems, please feel free to contact Jiang Jiedong.

3. Please write you code in a clean and readable way. You are encouraged to read other files and imitating them. This is necessary for you to understand the definitions. And please note that we will have more requirements on writing inline comments in future.

4. Currently, the whole design of this Euclidean Geometry project is still unstable, even for the very foundation files. It is possible to reformulate and reprove many currently existing theorems under the new design. As a result, building your proof dependent on fancier, later theorems is much better than building your proof on very elemental theorems (such as unfold everything). This is so called `de-couple`. It minimize the effort of implementing new designs, changing one place will not raise errors everywhere. We kindly ask you to follow this principle.

## Project Detail
Team 1 : Fills sorry's in Plane.lean, section length, and section existence in Ray.lean.

Team 2 : Fills sorry's in section coersion_compatibility and section midpoint Ray.lean

Team 3 : Fills sorry's in Ray_ex.lean

Team 4 : Fills sorry's in Line.lean

Team 5 : Fills sorry's in Line_ex.lean

Team 6 : Fills sorry's in Perpendicular.lean

Team 7 : Fills sorry's in Congruence.lean, but you may leave SAS blank and use SAS (and cosine theorem, sine theorem) to show other triangle congruence criteria.

Team 8 : Fills sorry's in IsocelesTriangle.lean
-/
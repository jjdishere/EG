/-
# Tips for creating a file in construction

## File Structure
The following assumes that there is a single new concept to define in the file. If a file contains more the 2 new concept to define (e.g. angle bisector and incenter are in the same file), please expand each of them following this instruction.

Broadly speaking, there are three kind of new concepts in Construction: A new class (e.g. Quadrilateral), A new construction (e.g. AngleBisector), A new property alone (e.g. IsParallelogram).

1. (only for class/construction) Prove the preparing theorems and define the class/construction;
2. (only for class) Define the make methods;
3. Define the predicate (e.g. IsAngleBisector IsParallelogram), if your new class extends some old class by adding new properties, you may also need to define a predicate `before` you can define thr class (e.g. Quadrilaterial.IsConvex); 
4. (only for class/construction) Compatibility of the predicate and your class/construction;
5. Criterion: theorems with your predicate in the conclusion;
6. Properties: theorems with your predicate in the condition.

## Minor Principles

1. We should stick to geometry as much as possible. Please avoid using vector calculations as possible. As a result, one avoids stating theorems using `Vec` or `Vec_nd` (either in conditions or conclusions).

2. 
-/
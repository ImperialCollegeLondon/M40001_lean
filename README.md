# M40001/M40009 example sheets and course notes in Lean.

M40001/M40009 is the "introduction to proof" course in the maths department at Imperial College London. I (Kevin Buzzard) am formalising the part of the course that I am running.

Over time expect course notes and example sheets to appear.

Current state: no course notes, but two example sheets.

# How to try the example sheets in Lean

## Try the example sheets online

[Sheet 1](https://tinyurl.com/M40001-Lean-sheet1)
[Sheet 2](https://tinyurl.com/M40001-Lean-sheet2)
[Sheet 3](https://tinyurl.com/M40001-Lean-sheet3)
[Sheet 4](https://tinyurl.com/M40001-Lean-sheet4)



## Download the project and try the example sheets on your own computer

This only works if you have Lean and mathlib installed. Instructions for installing Lean and mathlib are [here at the mathlib github repository](https://github.com/leanprover-community/mathlib#installation).

If lean and mathlib are installed, then install this project by typing this:

```
$ git clone git@github.com:ImperialCollegeLondon/M40001_lean.git
$ cd M40001_lean
/M40001_lean$ leanpkg configure
/M40001_lean$ update-mathlib
```

Then open the project folder using the "File -> Open Folder" option in VS Code and look in the `src/questions` directory for the problem sheets.

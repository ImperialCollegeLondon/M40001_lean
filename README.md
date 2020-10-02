# M40001/M40009 example sheets and other things in Lean.

M40001/M40009 is the "introduction to proof" course in the maths department at Imperial College London. In the 2020 directory I am currently putting the 2020 example sheets and some other little Lean files demonstrating things from the course.

## How to try the example sheets in Lean

You have two options: (1) use Lean online or (2) install it onto your computer.

### (1) : use Lean online.

Here are the problem sheets for October 2020:

[Sheet 1](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2020%2Fproblem_sheets%2Fsheet1.lean).

(more sheets to come).

Here are the 2019 sheets:

[Sheet 1](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2019%2Fquestions%2Fsheet1.lean).

[Sheet 2](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2019%2Fquestions%2Fsheet2.lean).

[Sheet 3](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2019%2Fquestions%2Fsheet3.lean).

[Sheet 4](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2019%2Fquestions%2Fsheet4.lean).

### (2) Download the project and try the example sheets on your own computer

This only works if you have the [Leanprover community tools installed](https://leanprover-community.github.io/get_started.html); these tools will give you a fully working Lean and mathlib on your computer.

Once you have that, then fire up the command line, change to the directory where you keep your Lean projects, and type this:

```
$ leanproject get ImperialCollegeLondon/M40001_lean
```

Then open the project in VS Code e.g. by selecting `File` -> `Open Folder` and then selecting the `M40001_lean` directory. Then look in the `src/2020/problem_sheets` directory for this year's problem sheets, and you can look at other Lean files in the 2020 directory too, such as the ones I've been using in the 2020 videos.

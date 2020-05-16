import .import1 .import2

/- this file tests that declararing the same or similar notation in two different files will rarely cause errors. We will get an error if we add the same command to the same namespace in the same environment in two different files, and then import them both. (e.g. if we remove `nat` in file `import2`. -/

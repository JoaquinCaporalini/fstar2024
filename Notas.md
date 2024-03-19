# Notas

## Como traigo los cambios desde el repo de guido?

- 1. ir a la carpeta del proyecto.

- 2. si nunca agregue el remoto de Guido, sino salto al 3 
```BASH
git remote add upstream https://github.com/mtzguido/verificacion-con-fstar-2024.git
```

- 3. Traigo los cambios del repositorio de Guido 
```bash
git fetch upstream
```
- 4. Los agrego a la rama actual
```bash
git merge upstream/main
```

## Practica 1

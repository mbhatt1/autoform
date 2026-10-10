"""`python -m autoform.nl <git-url|dir> [Module] ...` — same as `autoform autoformalize`."""
import sys

from .pipeline import main

sys.exit(main())

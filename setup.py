from pathlib import Path
import sys

from setuptools import setup

sys.path.insert(0, str(Path(__file__).resolve().parent))
from build_support import RuntimeBuild

setup(cmdclass={"build_py": RuntimeBuild})

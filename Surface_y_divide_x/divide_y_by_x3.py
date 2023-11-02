import matplotlib.pyplot as plt
import numpy as np

from matplotlib import cm
from matplotlib.ticker import LinearLocator
from cmath import pi

def f(x):    
    return x/np.sqrt(1 + x**2) 

def g(y):    
    return y/np.sqrt(1 - y**2) 

fig, ax = plt.subplots(subplot_kw={"projection": "3d"})
granularity = 0.001

numberOfPoints = 1/granularity - 2

# Make data.
radius = np.arange(granularity, 1- granularity, granularity)



# Make data

angle = np.arange(granularity, pi-granularity , (pi-granularity)/numberOfPoints)
T = np.outer(radius , np.cos(angle))
U = np.outer(radius, np.sin(angle))
X = np.outer(g(radius) , np.cos(angle))
Y = np.outer(g(radius), np.sin(angle))
Z = f(X/Y)
# Plot the surface.
surf1 = ax.plot_surface(T, U, Z, cmap=cm.coolwarm,
                       linewidth=0, antialiased=False)

# Make data.
angle = np.arange(pi + granularity, 2* pi-granularity , 
                 (pi-granularity)/numberOfPoints)

# Make data
T = np.outer(radius , np.cos(angle))
U = np.outer(radius, np.sin(angle))
X = np.outer(g(radius) , np.cos(angle))
Y = np.outer(g(radius), np.sin(angle))
Z = f(X/Y)
# Plot the surface.
#surf2 = ax.plot_surface(T, U, Z, cmap=cm.coolwarm,
#                       linewidth=0, antialiased=False)

# Customize the z axis.
ax.set_zlim(-1.01, 1.01)
ax.zaxis.set_major_locator(LinearLocator(10))
# A StrMethodFormatter is used automatically
ax.zaxis.set_major_formatter('{x:.02f}')

# Add a color bar which maps values to colors.
fig.colorbar(surf1, shrink=0.5, aspect=5)

plt.show()
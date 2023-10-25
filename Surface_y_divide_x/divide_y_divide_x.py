import matplotlib.pyplot as plt
import numpy as np

from matplotlib import cm
from matplotlib.ticker import LinearLocator

fig, ax = plt.subplots(subplot_kw={"projection": "3d"})
granularity = 0.001
# Make data.
X1 = np.arange(granularity, 3, granularity)
Y1 = np.arange(-3, -granularity, granularity) + np.arange(granularity, 3, granularity)
X1, Y1 = np.meshgrid(X1, Y1)
Z1 = (Y1/X1)/(np.sqrt(1 + Y1**2/X1**2))

# Plot the surface.
surf1 = ax.plot_surface(X1, Y1, Z1, cmap=cm.coolwarm,
                       linewidth=0, antialiased=False)

X2 = np.arange(-3, -granularity, granularity)
Y2 = np.arange(-3, -granularity, granularity) + np.arange(granularity, 3, granularity)
X2, Y2 = np.meshgrid(X2, Y2)
Z2 = (Y2/X2)/(np.sqrt(1 + Y2**2/X2**2))

surf2 = ax.plot_surface(X2, Y2, Z2, cmap=cm.coolwarm,
                       linewidth=0, antialiased=False)


# Customize the z axis.
ax.set_zlim(-1.01, 1.01)
ax.zaxis.set_major_locator(LinearLocator(10))
# A StrMethodFormatter is used automatically
ax.zaxis.set_major_formatter('{x:.02f}')

# Add a color bar which maps values to colors.
fig.colorbar(surf1, shrink=0.5, aspect=5)

plt.show()
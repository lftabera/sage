"""
Points

TESTS::

    sage: E = EllipticCurve('37a')
    sage: P = E(0,0)
    sage: def get_points(n): return sum([point(list(i*P)[:2], pointsize=3) for i in range(-n,n) if i != 0 and (i*P)[0] < 3])
    sage: sum([get_points(15*n).plot3d(z=n) for n in range(1,10)])
"""

from sage.plot.primitive import GraphicPrimitive_xydata
#*****************************************************************************
#       Copyright (C) 2006 Alex Clemesha <clemesha@gmail.com>,
#                          William Stein <wstein@gmail.com>,
#                     2008 Mike Hansen <mhansen@gmail.com>,
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************
from sage.plot.misc import options, rename_keyword
from sage.plot.colors import to_mpl_color

# TODO: create _allowed_options for 3D point classes to
# improve bad option handling in plot3d?
class Point(GraphicPrimitive_xydata):
    """
    Primitive class for the point graphics type.  See point?, point2d?
    or point3d? for information about actually plotting points.

    INPUT:

    - xdata - list of x values for points in Point object

    - ydata - list of y values for points in Point object

    - options - dict of valid plot options to pass to constructor

    EXAMPLES:

    Note this should normally be used indirectly via ``point`` and friends::

        sage: from sage.plot.point import Point
        sage: P = Point([1,2],[2,3],{'alpha':.5})
        sage: P
        Point set defined by 2 point(s)
        sage: P.options()['alpha']
        0.500000000000000
        sage: P.xdata
        [1, 2]

    TESTS:

    We test creating a point::

        sage: P = point((3,3))
    """
    def __init__(self, xdata, ydata, options):
        """
        Initializes base class Point.

        EXAMPLES::

            sage: P = point((3,4))
            sage: P[0].xdata
            [3.0]
            sage: P[0].options()['alpha']
            1
        """
        self.xdata = xdata
        self.ydata = ydata
        GraphicPrimitive_xydata.__init__(self, options)

    def _allowed_options(self):
        """
        Return the allowed options for the Point class.

        EXAMPLES::

            sage: P = point((3,4))
            sage: P[0]._allowed_options()['pointsize']
            'How big the point is.'
        """
        return {'alpha':'How transparent the line is.',
                'pointsize': 'How big the point is.',
                'faceted': 'If True color the edge of the point.',
                'rgbcolor':'The color as an RGB tuple.',
                'hue':'The color given as a hue.',
                'zorder':'The layer level in which to draw'}

    def _plot3d_options(self, options=None):
        """
        Translate 2D plot options into 3D plot options.

        EXAMPLES::

            sage: A=point((1,1),pointsize=22)
            sage: a=A[0];a
            Point set defined by 1 point(s)
            sage: b=a.plot3d()
            sage: b.size
            22
            sage: b=a.plot3d(size=3)
            sage: b.size
            3
        """
        if options == None:
            options = dict(self.options())
        options_3d = {}
        if 'pointsize' in options:
            options_3d['size'] = options['pointsize']
            del options['pointsize']
        if 'faceted' in options:
            if options['faceted']:
                raise NotImplementedError, "No 3d faceted points."
            del options['faceted']
        options_3d.update(GraphicPrimitive_xydata._plot3d_options(self, options))
        return options_3d

    def plot3d(self, z=0, **kwds):
        """
        Plots a two-dimensional point in 3-D, with default height zero.

        INPUT:


        -  ``z`` - optional 3D height above `xy`-plane.  May be a list
           if self is a list of points.

        EXAMPLES:

        One point::

            sage: A=point((1,1))
            sage: a=A[0];a
            Point set defined by 1 point(s)
            sage: b=a.plot3d()

        One point with a height::

            sage: A=point((1,1))
            sage: a=A[0];a
            Point set defined by 1 point(s)
            sage: b=a.plot3d(z=3)
            sage: b.loc[2]
            3.0

        Multiple points::

            sage: P=point([(0,0), (1,1)])
            sage: p=P[0]; p
            Point set defined by 2 point(s)
            sage: q=p.plot3d(size=22)

        Multiple points with different heights::

            sage: P=point([(0,0), (1,1)])
            sage: p=P[0]
            sage: q=p.plot3d(z=[2,3])
            sage: q.all[0].loc[2]
            2.0
            sage: q.all[1].loc[2]
            3.0

        Note that keywords passed must be valid point3d options::

            sage: A=point((1,1),pointsize=22)
            sage: a=A[0];a
            Point set defined by 1 point(s)
            sage: b=a.plot3d()
            sage: b.size
            22
            sage: b=a.plot3d(pointsize=23) # only 2D valid option
            sage: b.size
            22
            sage: b=a.plot3d(size=23) # correct keyword
            sage: b.size
            23

        TESTS:

        Heights passed as a list should have same length as
        number of points::

            sage: P=point([(0,0), (1,1), (2,3)])
            sage: p=P[0]
            sage: q=p.plot3d(z=2)
            sage: q.all[1].loc[2]
            2.0
            sage: q=p.plot3d(z=[2,-2])
            Traceback (most recent call last):
            ...
            ValueError: Incorrect number of heights given
        """
        from sage.plot.plot3d.base import Graphics3dGroup
        from sage.plot.plot3d.shapes2 import point3d
        options = self._plot3d_options()
        options.update(kwds)
        zdata=[]
        if type(z) is list:
            zdata=z
        else:
            zdata=[z]*len(self.xdata)
        if len(zdata)==len(self.xdata):
            all = [point3d([(x, y, z) for x, y, z in zip(self.xdata, self.ydata, zdata)], **options)]
            if len(all) == 1:
                return all[0]
            else:
                return Graphics3dGroup(all)
        else:
            raise ValueError, 'Incorrect number of heights given'

    def _repr_(self):
        """
        String representation of Point primitive.

        EXAMPLES::

            sage: P=point([(0,0), (1,1)])
            sage: p=P[0]; p
            Point set defined by 2 point(s)
        """
        return "Point set defined by %s point(s)"%len(self.xdata)

    def __getitem__(self, i):
        """
        Returns tuple of coordinates of point.

        EXAMPLES::

            sage: P=point([(0,0), (1,1), (2,3)])
            sage: p=P[0]; p
            Point set defined by 3 point(s)
            sage: p[1]
            (1.0, 1.0)
        """
        return self.xdata[i], self.ydata[i]

    def _render_on_subplot(self,subplot):
        r"""
        TESTS:

        We check to make sure that \#2076 is fixed by verifying all
        the points are red::

            sage: point(((1,1), (2,2), (3,3)), rgbcolor=hue(1), pointsize=30)
        """
        options = self.options()

        #Convert the color to a hex string so that the scatter
        #method does not interpret it as a list of 3 floating
        #point color specifications when there are
        #three points. This is mentioned in the matplotlib 0.98
        #documentation and fixes \#2076
        from matplotlib.colors import rgb2hex
        c = rgb2hex(to_mpl_color(options['rgbcolor']))

        a = float(options['alpha'])
        s = int(options['pointsize'])
        faceted = options['faceted'] #faceted=True colors the edge of point
        scatteroptions={}
        if not faceted: scatteroptions['edgecolors'] = 'none'

        subplot.scatter(self.xdata, self.ydata, s=s, c=c, alpha=a, **scatteroptions)

def point(points, **kwds):
    """
    Returns either a 2-dimensional or 3-dimensional point or sum of points.

    INPUT:

    -  ``points`` - either a single point (as a tuple) or a list of points.

    For information regarding additional arguments, see either point2d?
    or point3d?.

    EXAMPLES::

        sage: point((1,2))
        sage: point((1,2,3))
        sage: point([(0,0), (1,1)])
        sage: point([(0,0,1), (1,1,1)])

    Extra options will get passed on to show(), as long as they are valid::

        sage: point([(cos(theta), sin(theta)) for theta in srange(0, 2*pi, pi/8)], frame=True)
        sage: point([(cos(theta), sin(theta)) for theta in srange(0, 2*pi, pi/8)]).show(frame=True) # These are equivalent
    """
    try:
        return point2d(points, **kwds)
    except (ValueError, TypeError):
        from sage.plot.plot3d.shapes2 import point3d
        return point3d(points, **kwds)

@options(alpha=1, pointsize=10, faceted=False, rgbcolor=(0,0,1))
def point2d(points, **options):
    r"""
    A point of size ``pointsize`` defined by point = `(x,y)`.
    Point takes either a single tuple of coordinates or a list of tuples.

    Type ``point2d.options`` to see all options.

    EXAMPLES:

    A purple point from a single tuple or coordinates::

        sage: point((0.5, 0.5), rgbcolor=hue(0.75))

    If you need a 2D point to live in 3-space later,
    this is possible::

        sage: A=point((1,1))
        sage: a=A[0];a
        Point set defined by 1 point(s)
        sage: b=a.plot3d(z=3)

    This is also true with multiple points::

        sage: P=point([(0,0), (1,1)])
        sage: p=P[0]
        sage: q=p.plot3d(z=[2,3])

    Here are some random larger red points, given as a list of tuples::

        sage: point(((0.5, 0.5), (1, 2), (0.5, 0.9), (-1, -1)), rgbcolor=hue(1), pointsize=30)

    Extra options will get passed on to show(), as long as they are valid::

        sage: point([(cos(theta), sin(theta)) for theta in srange(0, 2*pi, pi/8)], frame=True)
        sage: point([(cos(theta), sin(theta)) for theta in srange(0, 2*pi, pi/8)]).show(frame=True) # These are equivalent
    """
    from sage.plot.plot import xydata_from_point_list, Graphics
    xdata, ydata = xydata_from_point_list(points)
    g = Graphics()
    g._set_extra_kwds(Graphics._extract_kwds_for_show(options))
    g.add_primitive(Point(xdata, ydata, options))
    return g

points = point

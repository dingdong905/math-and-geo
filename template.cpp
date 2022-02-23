#include<string>
#include<vector>
#include<deque>
#include<ctime>
#include<cmath>
#include<iostream>
#include<cassert>
#include<algorithm>
#include<cstring>
#include<unordered_map>
#include<map>
#include<set>
using namespace std;
namespace pre{
	using namespace std;
	#define io ios::sync_with_stdio(false);cin.tie(0);
	typedef long long ll;
	typedef long double ld;
	const int inf=(1<<30);
	const long double eps=1e-8;
	const long double pi=acos((long double)-1.0);
	typedef long long ll;
	const ll mod=1e9+7;
	const ll mod2=998244353;
	const ll mod3=1004535809;
	const int maxn=1e6+5;
	const ll linf=1LL<<62;
	inline bool _zero(double x){return (((x)>0?(x):-(x))<eps);}
	inline double _sq(double x){return x*x;}
	inline ll sqr(ll a){return a*a;}
	inline int _sign(double x){return ((x)>eps?1:((x)<-eps?2:0));}
}
namespace geo{
	using namespace pre; 
	struct Point{//point(x,y) 
	    double x,y;
	    Point():x(0),y(0){}
	    Point(double x,double y): x(x),y(y) {}
	    friend istream& operator >>(istream &in,Point &p){
			in>>p.x>>p.y;
			return in;
		} 
		friend ostream& operator <<(ostream &out,const Point &p){
			out<<p.x<<" "<<p.y;
			return out;
		}
	    Point operator + (Point b) const {return Point(x+b.x,y+b.y);}
	    Point operator - (Point b) const {return Point(x-b.x,y-b.y);}
	    Point operator * (double b) const {return Point(b*x,b*y);}
	    double operator * (Point b) const {return x*b.y-y*b.x;}
	    double operator & (Point b) const {return x*b.x+y*b.y;}
	    double distance() const {return sqrt(_sq(x)+_sq(y));}
	    Point unit() const {return Point(x/distance(),y/distance());}
	    bool operator < (const Point &b) const{//compare by polar
			return (*this)*b>eps || _zero((*this)*b) && distance()<b.distance();
		}
		static bool comp(const Point &a,const Point &b){//compare by coordinate
			return a.y<b.y || a.y==b.y && a.x<b.x;
		}
	    double distance(Point p) const {
			return (*(this)-p).distance();
		}
	    double distance(Point p1,Point p2) const {
			return (p2-p1).distance();
		}
	    double xmult(Point p1,Point p2) const {//calculate a cross-mult base on itself
			return (p1-(*this))*(p2-(*this));
		}
	    double dmult(Point p1,Point p2) const {//calculate a dot-mult base on itself
			return (p1-(*this))&(p2-(*this));
		}
	    bool dots_inline(Point p1,Point p2) const{//three points in a line
	        return _zero(xmult(p1,p2));
		}
	    Point rotate(Point p,double angle,double scale){ //base on Point contrarotate(anticlockwise) angle and enlarge scale times
	        Point ret=p;
	        x-=p.x,y-=p.y;
	        p.x=scale*cos(angle);
	        p.y=scale*sin(angle);
	        ret.x+=x*p.x-y*p.y;
	        ret.y+=x*p.y+y*p.x;
	        return ret;
	    }
	    double rag(Point a,Point b)const{//included angle
			return acos((_sq(distance(a))+_sq(distance(b))-_sq(a.distance(b)))/(2*distance(a)*distance(b)));
		}
		Point pedal() const{
			return Point(y,-x);
		}
	};
	struct Polar//polar(radius,theta)
	{
	    double radius,theta;
	    Polar():radius(0),theta(0){}
	    Polar(double theta):radius(1),theta(theta){}
	    Polar(double radius,double theta):radius(radius),theta(theta){}
	    Polar(Point p):radius(p.distance()),theta(atan2(p.y,p.x)){}
	    friend istream& operator >>(istream &in,Polar &p){
			in>>p.radius>>p.theta;
			return in;
		} 
		friend ostream& operator <<(ostream &out,const Polar &p){
			out<<p.radius<<" "<<p.theta;
			return out;
		}
	    bool operator < (const Polar &b)const{return theta<b.theta || theta==b.theta && radius<b.radius;}
	    Point topoint(){	//to point
			return Point(radius*cos(theta),radius*sin(theta));
		}
	    Polar unit(){	//unit circle
			return Polar(theta);
		}
	};
	struct Line{//line
	    Point a,b;
	    Line(): a(Point()),b(Point()){}
	    Line(Point a,Point b): a(a),b(b) {}
	    friend istream& operator >>(istream &in,Line &l){
			in>>l.a>>l.b;
			return in;
		} 
		friend ostream& operator <<(ostream &out,const Line &l){
			out<<l.a<<" "<<l.b;
			return out;
		}
	    Point midpoint() const {//mid point
			return (a+b)*0.5;
		}
	    double distance() const {//length
			return a.distance(b);
		}
	    bool dot_inline(Point p) {//if point in line
			return _zero(p.xmult(a,b));
		}
	    bool dot_online(Point p) {//if point in segment
			return _zero(p.xmult(a,b))&&(a.x-p.x)*(b.x-p.x)<eps&&(a.y-p.y)*(b.y-p.y)<eps;
		}
	    bool dot_online_in(Point p){//if point in segment except two point
			return dot_online(p)&&(!_zero(p.x-a.x)||!_zero(p.y-a.y))&&(!_zero(p.x-b.x)||!_zero(p.y-b.y));
		}
	    bool same_side(Point p1,Point p2){//if two points on same side except line
			return a.xmult(b,p1)*a.xmult(b,p2)>eps;
		}
	    bool opposite_side(Point p1,Point p2){//if two points on opposite side except line
			return a.xmult(b,p1)*a.xmult(b,p2)<-eps;
		}
	    bool parallel(Line v){//if two lines parallel
			return _zero(Point().xmult(a-b,v.a-v.b));
		}
		bool parallel_ex(Line v){//if two lines parallel and not coincidence 
			return _zero(Point().xmult(a-b,v.a-v.b))&&!dot_inline(v.a); 
		}
	    bool perpendicular(Line v){//if two lines perpendicular
			return _zero(Point().dmult(a-b,v.a-v.b));
		}
	    bool intersect(Line v){//if two segments have same points
	        return !same_side(v.a,v.b)&&!v.same_side(a,b);
	    }
	    bool intersect_ex(Line v){//if two segments have only same point except end points
			return opposite_side(v.a,v.b)&&v.opposite_side(a,b);
		}
	    Point intersection(Line v){//calculate the intersection of two lines,please notice they are not parallel
	        Point ret=a;
	        double t=((a.x-v.a.x)*(v.a.y-v.b.y)-(a.y-v.a.y)*(v.a.x-v.b.x))
	                /((a.x-b.x)*(v.a.y-v.b.y)-(a.y-b.y)*(v.a.x-v.b.x));
	        return a+(b-a)*t;
	    } 
	    Point pedal(Point p){//calculate the nearest point to the line,pedal  
	        Point t=p;
	        t.x+=a.y-b.y,t.y+=b.x-a.x;
	        if(dot_inline(p)) return p; 
	        return intersection(Line(p,t));
	    }
	    double distance(Point p){//calculate the distance from point to line
			return fabs(b.xmult(p,a))/distance();
		}
	    Point ptoseg(Point p){//calculate the nearest point to the segment 
	        Point t=p;
	        t.x+=a.y-b.y,t.y+=b.x-a.x;
	        if (p.xmult(a,t)*p.xmult(b,t)>eps)
	            return a.distance(p)<b.distance(p)?a:b;
	        return pedal(p);
	    }
	    double disptoseg(Point p){//calculate the distance from point to segment
	        Point t=p;
	        t.x+=a.y-b.y,t.y+=b.x-a.x;
	        if (p.xmult(a,t)*p.xmult(b,t)>eps)
	            return Line(p,a).distance()<Line(p,b).distance()?Line(p,a).distance():Line(p,b).distance();
	        return fabs(b.xmult(p,a))/distance();
	    }
	    Line midperpendicular(){
	    	return Line(midpoint(),midpoint()+(b-a).pedal());
		}
		Point definite_point(double rate){
			Point v=b-a;
			return a+v*rate;
		} 
	};
	struct General_line// ax+by+c=0 for general line expression exp 
	{
	    double a,b,c;
	    General_line():a(0),b(0),c(0){}
	    General_line(double a,double b,double c):a(a),b(b),c(c){}
	    General_line(Line l):a((l.a-l.b).y),b(-(l.a-l.b).x),c(-a*l.a.x-b*l.a.y){}
	    friend istream& operator >>(istream &in,General_line &l){
			in>>l.a>>l.b>>l.c;
			return in;
		} 
		friend ostream& operator <<(ostream &out,const General_line &l){
			out<<l.a<<" "<<l.b<<" "<<l.c;
			return out;
		}
	    Point symmetricalPointofLine(Point p){//calculate symmetric point of the line
	    
	        double d=_sq(a)+_sq(b);
	        return Point((_sq(b)*p.x-_sq(a)*p.x-2*a*b*p.y-2*a*c)/d,(_sq(a)*p.y-_sq(b)*p.y-2*a*b*p.x-2*b*c)/d);
	    }
	};
	struct Circle//circle(point,radius)
	{
	    Point center;
	    double radius;
	    Circle():center(Point()),radius(0){}
	    Circle(Point center,double radius):center(center),radius(radius){}
	    Circle(Line l): center(l.midpoint()),radius(l.distance()/2){}//diameter for a circle
	    friend istream& operator >>(istream &in,Circle &c){
			in>>c.center>>c.radius;
			return in;
		} 
		friend ostream& operator <<(ostream &out,const Circle &c){
			out<<c.center<<" "<<c.radius;
			return out;
		}
	    Circle(Point p1,Point p2,Point p3){//three points for a circle
	    	Line u,v;
	        u.a=Line(p1,p2).midpoint();
	        u.b=Line(p1,p2).pedal(p3);
	        v.a=Line(p1,p3).midpoint();
	        v.b=Line(p1,p3).pedal(p2);
			center=u.intersection(v);
			radius=center.distance(p1);
		}
	    double area() const{//the area
		
			return pi*_sq(radius);
		}	
	    double perimeter(){//the perimeter 
	    	return 2.0*pi*radius;
		}
	    bool inside_circle(Point p){//if point in circle
			return center.distance(p)<radius+eps;
		}
	    bool intersect(Line l){//if line and circle have intersection
			return l.distance(center)<radius+eps;
		}
	    bool intersect_ex(Line l){//if segment and circle have intersection
	        double t1=center.distance(l.a)-radius,t2=center.distance(l.b)-radius;
	        Point t=center;
	        if (t1<eps||t2<eps)
	            return t1>-eps||t2>-eps;
	        t.x+=l.a.y-l.b.y;
	        t.y+=l.b.x-l.a.x;
	        return t.xmult(l.a,center)*t.xmult(l.b,center)<eps&&l.distance(center)-radius<eps;
	    }
	    bool intersect(Circle c2){//if two circles have intersection
			return center.distance(c2.center)<radius+c2.radius+eps&&center.distance(c2.center)>fabs(radius-c2.radius)-eps;
		}
	    int circleposition(Circle c2){	//relative location of two circles
	        double d=center.distance(c2.center),rs=radius+c2.radius,rd=radius-c2.radius;
	        if (_zero(d)&&_zero(rd)) return -2;//coincidence
	        if (_zero(rs-d)) return 4;//circumscribed
	        if (_zero(rd-d)) return 3;//inscribe and c2 in c
	        if (_zero(rd+d)) return -3;//inscribe and c in c2
	        if (d>rs) return 0;//separation of two circles from outside
	        if (intersect(c2)) return 2;//circle intersection
	        if (rd>0) return 1;//separation of two circles and c2 in c
	        return -1; //separation of two circles and c in c2
	    }
		double intersection_area(Circle c2){
			double dis=center.distance(c2.center);
			if(radius+c2.radius<=dis)
	        	return 0.0;
	    	if(radius-c2.radius>=dis)
	        	return c2.area();
	    	if(c2.radius-radius>=dis)
	        	return area();
	    	double angle1 =acos((_sq(radius)+_sq(dis)-_sq(c2.radius))/(2*dis*radius));
	    	double angle2 =acos((_sq(c2.radius)+_sq(dis)-_sq(radius))/(2*dis*c2.radius));
	    	return _sq(radius)*angle1+_sq(c2.radius)*angle2-sin(angle1)*radius*dis;
		}
		Point intersection(Circle c2){//use if have intersection and return one of it 
			double dis=center.distance(c2.center);
			Point p1=(center+c2.center)*0.5,p2=(c2.center-center)*0.5;
			double i1=(_sq(radius)-_sq(c2.radius))/(_sq(dis)),i2=sqrt(2*(_sq(radius)+_sq(c2.radius))/(_sq(dis))-_sq(i1)-1);
			return p1+p2*i1+Point(p2.y,p2.x)*i2;
		}
		double distance(Point p){
			double dis=p.distance(center)-radius;
			if(dis<0) return 0.0;
			else return dis;
		}
		double distance(Line l){
			double dis=l.distance(center)-radius;
			if(dis<0) return 0.0;
			else return dis;
		}
		double disptoseg(Line l){
			double dis=l.disptoseg(center)-radius;
			if(dis<0) return 0.0;
			else return dis;
		}
	};
	struct Triangle{//triangle
	    vector<Point> p;
	    Triangle(){p.resize(3);}
	    Triangle(Point a,Point b,Point c){p.resize(3);p[0]=a;p[1]=b;p[2]=c;}
	    double area()//the area
	    {
	        return fabs(p[0].xmult(p[1],p[2]))/2;
	    }
	    Point perpencenter()//the perpencenter,orthocenter of a triangle
	    {
	        Line u,v;
	        u.a=p[2];
	        u.b=Line(p[0],p[1]).pedal(p[2]);
	        v.a=p[1];
	        v.b=Line(p[0],p[2]).pedal(p[1]);
	        return u.intersection(v);
	    }
	    Point barycenter()//the barycenter of triangle,it's the point of lowest sum of square of distance to three points,it's the point of largest product of square of distance to three points in triangle
	    {
	        Line u,v;
	        u.a=Line(p[0],p[1]).midpoint();
	        u.b=p[2];
	        v.a=Line(p[0],p[2]).midpoint();
	        v.b=p[1];
	        return u.intersection(v);
	    }
	    Point circumcenter()//excenter of a triangle
	    {
	        Point tmp;
			tmp.x=p[0].x+(0.5*(_sq(p[1].x-p[0].x)+_sq(p[1].y-p[0].y))*(p[2].y-p[0].y)-0.5*(_sq(p[2].x-p[0].x)+_sq(p[2].y-p[0].y))*(p[1].y-p[0].y))/((p[1].x-p[0].x)*(p[2].y-p[0].y)-(p[2].x-p[0].x)*(p[1].y-p[0].y));
			tmp.y=p[0].y+(0.5*(_sq(p[2].x-p[0].x)+_sq(p[2].y-p[0].y))*(p[1].x-p[0].x)-0.5*(_sq(p[1].x-p[0].x)+_sq(p[1].y-p[0].y))*(p[2].x-p[0].x))/((p[1].x-p[0].x)*(p[2].y-p[0].y)-(p[2].x-p[0].x)*(p[1].y-p[0].y));
	        return tmp;
	    }
	    Point incenter()//incenter of a triangle
	    {
	        Line u,v;
	        double m,n;
	        u.a=p[0];
	        m=atan2(p[1].y-p[0].y,p[1].x-p[0].x);
	        n=atan2(p[2].y-p[0].y,p[2].x-p[0].x);
	        u.b.x=u.a.x+cos((m+n)/2);
	        u.b.y=u.a.y+sin((m+n)/2);
	        v.a=p[1];
	        m=atan2(p[0].y-p[1].y,p[0].x-p[1].x);
	        n=atan2(p[2].y-p[1].y,p[2].x-p[1].x);
	        v.b.x=v.a.x+cos((m+n)/2);
	        v.b.y=v.a.y+sin((m+n)/2);
	        return u.intersection(u);
	    }
	    Point fermentpoint(){//ferment point,the point of lowest sum of distance to three points
	    
	        Point u,v;
	        double step=fabs(p[0].x)+fabs(p[0].y)+fabs(p[1].x)+fabs(p[1].y)+fabs(p[2].x)+fabs(p[2].y);
	        int i,j,k;
	        u.x=(p[0].x+p[1].x+p[2].x)/3;
	        u.y=(p[0].y+p[1].y+p[2].y)/3;
	        while (step>eps)
	            for (k=0;k<10;step/=2,k++)
	                for (i=-1;i<=1;i++)
	                    for (j=-1;j<=1;j++){
	                        v.x=u.x+step*i;
	                        v.y=u.y+step*j;
	                        if (u.distance(p[0])+u.distance(p[1])+u.distance(p[2])>v.distance(p[0])+v.distance(p[1])+v.distance(p[2]))
	                            u=v;
	                    }
	        return u;
	    }
	    Circle circumcircle(){//the circumcircle of the triangle
	    
	        Circle tmp;
			tmp.center.x=p[0].x+(0.5*(_sq(p[1].x-p[0].x)+_sq(p[1].y-p[0].y))*(p[2].y-p[0].y)-0.5*(_sq(p[2].x-p[0].x)+_sq(p[2].y-p[0].y))*(p[1].y-p[0].y))/((p[1].x-p[0].x)*(p[2].y-p[0].y)-(p[2].x-p[0].x)*(p[1].y-p[0].y));
			tmp.center.y=p[0].y+(0.5*(_sq(p[2].x-p[0].x)+_sq(p[2].y-p[0].y))*(p[1].x-p[0].x)-0.5*(_sq(p[1].x-p[0].x)+_sq(p[1].y-p[0].y))*(p[2].x-p[0].x))/((p[1].x-p[0].x)*(p[2].y-p[0].y)-(p[2].x-p[0].x)*(p[1].y-p[0].y));
	        tmp.radius=tmp.center.distance(p[0]);
			return tmp;    
	    }
	};
	struct Polygon{ //polygon
	    int n;
	    vector<Point> p;
	    Polygon(): n(0){}
	    Polygon(int n,Point* p0): n(n) {for (int i=0;i<n;i++) p.push_back(p0[i]);}
	    Polygon(int n,vector<Point> p0): n(n) {p.assign(p0.begin(),p0.end());}
	    Polygon(vector<Point> p0): n(p0.size()) {p.assign(p0.begin(),p0.end());}
	    friend istream& operator >>(istream &in,Polygon &x){
			in>>x.n;
			x.p.resize(x.n);
			for(int i=0;i<x.n;i++)
				in>>x.p[i];
			return in;
		} 
		friend ostream& operator <<(ostream &out,const Polygon &x){
			for(int i=0;i<x.p.size();i++) cout<<x.p[i]<<endl;
			return out;
		}
	    bool is_convex(){//if this is convex,edge collinear
	        int i,s[3]={1,1,1};
	        for (i=0;i<n&&s[1]|s[2];i++)
	            s[_sign(p[i].xmult(p[(i+1)%n],p[(i+2)%n]))]=0;
	        return s[1]|s[2];
	    }
	    bool is_convex_ex(){//if this is convex,no edge collinear
	        int i,s[3]={1,1,1};
	        for (i=0;i<n&&s[0]&&s[1]|s[2];i++)
	            s[_sign(p[i].xmult(p[(i+1)%n],p[(i+2)%n]))]=0;
	        return s[0]&&s[1]|s[2];
	    }
	    bool inside_convex(Point q){ //if point in convex
	        int i,s[3]={1,1,1};
	        for (i=0;i<n&&s[1]|s[2];i++)
	            s[_sign(p[i].xmult(p[(i+1)%n],q))]=0;
	        return s[1]|s[2];
	    }
	    bool inside_convex_ex(Point q){//if point in convex,except edge
	        int i,s[3]={1,1,1};
	        for (i=0;i<n&&s[0]&&s[1]|s[2];i++)
	            s[_sign(p[i].xmult(p[(i+1)%n],q))]=0;
	        return s[0]&&s[1]|s[2];
	    }
	    int inside_polygon(Point q,int on_edge=1){//if point in polygon,if on edge return on_edge
	        Point q2;
	        int i=0,count;
	        while (i<n)
	            for (count=i=0,q2.x=rand()+10000,q2.y=rand()+10000;i<n;i++)
	                if (_zero(p[(i+1)%n].xmult(q,p[i]))&&(p[i].x-q.x)*(p[(i+1)%n].x-q.x)<eps&&(p[i].y-q.y)*(p[(i+1)%n].y-q.y)<eps)
	                    return on_edge;
	                else if (_zero(p[i].xmult(q,q2)))
	                    break;
	                else if (q2.xmult(q,p[i])*q2.xmult(q,p[(i+1)%n])<-eps&&p[(i+1)%n].xmult(p[i],q)*p[(i+1)%n].xmult(p[i],q2)<-eps)
	                    count++;
	        return count&1;
	    }
	    int inside_polygon(Line l)////if segments in convex include edge
	    {
	        Point l1=l.a,l2=l.b,tt;
	        vector<Point> t;
	        int i,j;
	        if (!inside_polygon(l1)||!inside_polygon(l2))
	            return 0;
	        for (i=0;i<n;i++)
	            if (Line(p[i],p[(i+1)%n]).opposite_side(l1,l2)&&l.opposite_side(p[i],p[(i+1)%n]))
	                return 0;
	            else if (Line(p[i],p[(i+1)%n]).dot_online_in(l1))
	                t.push_back(l1);
	            else if (Line(p[i],p[(i+1)%n]).dot_online_in(l2))
	                t.push_back(l2);
	            else if (Line(l1,l2).dot_online_in(p[i]))
	                t.push_back(p[i]);
	        for (i=0;i<t.size();i++)
	            for (j=i+1;j<t.size();j++){
	                tt.x=(t[i].x+t[j].x)/2;
	                tt.y=(t[i].y+t[j].y)/2;
	                if (!inside_polygon(tt))
	                    return 0;          
	            }
	        return 1;
	    }
	    Point barycenter(){//the barycenter of the polygon
	        Point ret,t;
	        double t1=0,t2;
	        int i;
	        ret.x=ret.y=0;
	        for (i=1;i<n-1;i++)
	            if (fabs(t2=p[i+1].xmult(p[0],p[i]))>eps){
	                t=Triangle(p[0],p[i],p[i+1]).barycenter();
	                ret.x+=t.x*t2;
	                ret.y+=t.y*t2;
	                t1+=t2;
	            }
	        if (fabs(t1)>eps)
	            ret.x/=t1,ret.y/=t1;
	        return ret;
	    }
	    double area(){//the area of the polygon
	        double s1=0,s2=0;
	        for(int i=0;i<n;i++)
	            s1+=p[(i+1)%n].y*p[i].x,s2+=p[(i+1)%n].y*p[(i+2)%n].x;
	        return fabs(s1-s2)/2;
	    }
	    double perimeter(){//the perimeter of the polygon
			double pm=0;
			if(n>1) pm=p[n-1].distance(p[0]);
			for(int i=0;i<n-1;i++)
				pm+=p[i].distance(p[i+1]);
			return pm;
		} 
	    Polygon graham(){//Calculate the convex of polygon or points
	        Polygon g=(*this);
	        if(g.n<3) return g; 
	        sort(g.p.begin(),g.p.end(),Point().comp);
	        Point bp=g.p[0];
	        for(int i=0;i<g.n;i++) g.p[i]=g.p[i]-bp;
	        sort(g.p.begin(),g.p.end());
	        Polygon gra;
	        gra.p.push_back(g.p[0]);
	        gra.p.push_back(g.p[1]);
			int i=2;
			for(i=2;i<n;i++)
			{
				while(gra.p.size()>1&&gra.p[gra.p.size()-2].xmult(gra.p[gra.p.size()-1],g.p[i])<eps) //<eps 绝对凸包 <-eps 带180角凸包 
					gra.p.pop_back();
				gra.p.push_back(g.p[i]);
			}
			gra.n=gra.p.size();
			for(int i=0;i<gra.n;i++) gra.p[i]=gra.p[i]+bp;
	        return gra;
	    }
		Circle mincircle(){//calculate the min circle to cover polygon or points 
			Polygon g=*this;
	    	random_shuffle(g.p.begin(),g.p.end()); 
	    	Circle ans;
	    	ans=Circle(g.p[0],0);
			Point &c=ans.center;
			double &r=ans.radius;
		    for(int i=1;i<n;i++)
			{
		        if(c.distance(g.p[i])>r+eps)
				{ 
		            ans=Circle(g.p[i],0);
		            for(int j=0;j<i;j++)
					{
		                if(c.distance(g.p[j])>r+eps)
						{ 
		                    ans=Circle(Line(g.p[i],g.p[j]).midpoint(),g.p[i].distance(g.p[j])/2);
		                    for(int k=0;k<j;k++) {
		                        if(c.distance(g.p[k])>r+eps)
								{ 
			                        ans=Triangle(g.p[i],g.p[j],g.p[k]).circumcircle();
		                        }
		                    }
		                }
		            }
		        }
	    	}
	    	return ans;
		}
		double rotate_calipers(){
			Polygon convex=graham();
			if(convex.n<2) return 0;
			double ans=convex.p[0].distance(convex.p[1]);
			int q=1;
			for(int i=0;i<convex.n;i++)
		    {
		    	while(convex.p[(i+1)%convex.n].xmult(convex.p[q],convex.p[i])<convex.p[(i+1)%convex.n].xmult(convex.p[(q+1)%convex.n],convex.p[i]))
		           q=(q+1)%convex.n;
		        ans=max(ans,max(convex.p[q].distance(convex.p[i]),convex.p[(q+1)%convex.n].distance(convex.p[(i+1)%convex.n])));
		    }
		    return ans;
		}
	};
}
namespace mat{
	using namespace pre; 
	
	ll mul(ll a, ll b,ll _mod=mod){return ((__int128)a*b)%_mod;}
	ll mul2(ll a,ll b,ll _mod=mod){return ((a*b-(ll)((ll)((long double)a/_mod*b)*_mod))%_mod+_mod)%_mod;}
	ll mul3(ll a,ll b,ll _mod=mod){//special multiplications 
		a%=_mod,b%=_mod;
		ll ret=0;
		while(b){
			if(b&1) ret+=a,ret%=_mod;
			a<<=1,a%=_mod,b>>=1;
		}
		return ret;
	}
	ll gcd(ll a,ll b){
		if(a<0) a=-a;
		if(b<0) b=-b;
		if(a==0) return b;
		if(b==0) return a;
		while(a^=b^=a^=b%=a);
		return b; 
	}
	ll lcm(ll a,ll b){return a/gcd(a,b)*b;}
	ll exgcd(ll a,ll b,ll &x,ll &y){//exgcd can solve  ax+by=gcd(a,b) 
		if(b){
			ll c=exgcd(b,a%b,x,y),t=x;
			x=y,y=t-a/b*y;
			return c;
		}
		else{
			x=1,y=0;
			return a;
		}
	}
	ll inv(ll a,ll _mod=mod){//multiplicative inverse for exgcd 
		ll x,y,d=exgcd(a,_mod,x,y);
		if(d==1) return ((x%_mod)+_mod)%_mod;
		return -1;
	}
	ll phi(ll n){//eular(x)  if(x==prime)eular(x)=x-1 and a^k=a^(k%(x-1)) _mod x 
	    ll res=n;
	    for (ll i=2;i*i<=n;i++)
	        if(n%i==0)
	        {
	            res=res-res/i;
	            while(n%i==0)n/=i;
	        }
	    if(n>1)res=res-res/n;
	    return res;
	}
	ll qpow(ll x,ll n,ll _mod=mod,ll _mul(ll,ll,ll)=mul){// quick_pow 
		ll tmp=x%_mod,ret=1;
		if(n<0)
			n=-n,tmp=inv(tmp,_mod);
		while(n)
		{
			if(n&1)ret=_mul(ret,tmp,_mod);
			tmp=_mul(tmp,tmp,_mod);
			n>>=1;
		}
		return ret;
	}
	struct Complex{//complex
		long double x,y;
		Complex(long double x=0.0,long double y=0.0):x(x),y(y){}
	    friend istream& operator >>(istream &in,Complex &c)
		{
			in>>c.x>>c.y;
			return in;
		} 
		friend ostream& operator <<(ostream &out,const Complex& c)
		{
			out<<c.x<<" "<<c.y;
			return out;
		}
		Complex exp(long double theta=0,long double r=1){
			x=r*cos(theta),y=r*sin(theta);
			return *this;
		}
		friend long double abs(const Complex _t){return sqrt(sqr(_t.x)+sqr(_t.y));}
		friend long double re(const Complex _t){return _t.x;}
		friend long double im(const Complex _t){return _t.y;}
	    Complex operator-(const Complex b)const {return Complex(x-b.x,y-b.y);}
	    Complex operator+(const Complex b)const {return Complex(x+b.x,y+b.y);}
	    Complex operator*(const Complex b)const {return Complex(x*b.x-y*b.y,x*b.y+y*b.x);}
		Complex operator/(const Complex b)const {return Complex((x*b.x+y*b.y)/sqr(abs(b)),(-x*b.y+y*b.x)/sqr(abs(b)));}
		Complex qpow(ll n){
			Complex tmp=*this,ret=Complex(1);
			while(n)
			{
				if(n&1)ret=ret*tmp;
				tmp=tmp*tmp;
				n>>=1;
			}
			return ret;
		}
	};
	struct Vec{//vector
		int n;
		vector<ll> a;
		ll _mod=mod;
		Vec(int n=2,ll k=0):n(n){
			a.resize(n,k);
		}
	    friend istream& operator >>(istream &in,Vec &v)
		{
			in>>v.n;
			v.a.resize(v.n);
			for(int i=0;i<v.n;i++) in>>v.a[i];
			return in;
		} 
		friend ostream& operator <<(ostream &out,const Vec &v)
		{
			for(int i=0;i<v.n;i++) out<<v.a[i]<<(i==v.n-1?"\n":"");
			return out;
		}
		Vec zeros(){
			for(int i=0;i<n;i++)
				a[i]=0;
			return *this;
		}
		Vec eyes(){
			for(int i=0;i<n;i++)
				a[i]=1;
			return *this;
		}
		Vec operator*(Vec &b){
			assert(b.n==n);
			Vec ans=Vec(n,0);
			for(int i=0;i<n;i++)
				ans.a[i]+=a[i]%_mod*(b.a[i]%_mod)%_mod,
				ans.a[i]%=_mod;
			return ans;
		}
		Vec operator+(Vec &b){
			assert(b.n==n);
			Vec ans=Vec(n,0);
			for(int i=0;i<n;i++)
				ans.a[i]=a[i]+b.a[i],
				ans.a[i]%=_mod;
			return ans;
		}
		Vec operator-(Vec &b){
			assert(b.n==n);
			Vec ans=Vec(n,0);
			for(int i=0;i<n;i++)
				ans.a[i]=a[i]-b.a[i],
				ans.a[i]%=_mod;
			return ans;
		}
		Vec qpow(ll n){
			Vec tmp=*this,ret=*this;
			ret.eyes();
			while(n)
			{
				if(n&1)ret=ret*tmp;
				tmp=tmp*tmp;
				n>>=1;
			}
			return ret;
		} 
	};
	struct Matrix{//matrix 
		int n;
		vector<vector<ll> > a;
		ll _mod=mod;
		Matrix(int n=2,ll k=0):n(n){
			a.resize(n);
			for(int i=0;i<a.size();i++)
				a[i].resize(n,k);
		}
	    friend istream& operator >>(istream &in,Matrix &m)
		{
			in>>m.n;
			m.a.resize(m.n);
			for(int i=0;i<m.a.size();i++)
				m.a[i].resize(m.n);
			for(int i=0;i<m.n;i++)
			for(int j=0;j<m.n;j++) 
				in>>m.a[i][j];
			return in;
		} 
		friend ostream& operator <<(ostream &out,const Matrix &m)
		{
			for(int i=0;i<m.n;i++) 
			for(int j=0;j<m.n;j++) 
				out<<m.a[i][j]<<(j==m.n-1?(i==m.n-1?"":"\n"):" ");
			return out;
		}
		Matrix zeros(){
			for(int i=0;i<n;i++)
			for(int j=0;j<n;j++)
				a[i][j]=0;
			return *this;
		}
		Matrix ones(){
			for(int i=0;i<n;i++)
			for(int j=0;j<n;j++)
				a[i][j]=1;
			return *this;
		}
		Matrix eyes(){
			for(int i=0;i<n;i++)
			for(int j=0;j<n;j++)
				a[i][j]=(i==j);
			return *this;
		}
		Matrix operator*(Matrix &b){
			assert(b.n==n);
			Matrix ans=Matrix(n,0);
			for(int i=0;i<n;i++)
			for(int j=0;j<n;j++)
			for(int k=0;k<n;k++)
				ans.a[i][j]+=a[i][k]%_mod*(b.a[k][j]%_mod)%_mod,
				ans.a[i][j]%=_mod;
			return ans;
		}
		Matrix operator+(Matrix &b){
			assert(b.n==n);
			Matrix ans=Matrix(n,0);
			for(int i=0;i<n;i++)
			for(int j=0;j<n;j++)
				ans.a[i][j]=a[i][j]+b.a[i][j],
				ans.a[i][j]%=_mod;
			return ans;
		}
		Matrix operator-(Matrix &b){
			assert(b.n==n);
			Matrix ans=Matrix(n,0);
			for(int i=0;i<n;i++)
			for(int j=0;j<n;j++)
				ans.a[i][j]=a[i][j]-b.a[i][j],
				ans.a[i][j]%=_mod;
			return ans;
		}
		Matrix qpow(ll n){
			Matrix tmp=*this,ret=*this;
			ret.eyes();
			while(n)
			{
				if(n&1)ret=ret*tmp;
				tmp=tmp*tmp;
				n>>=1;
			}
			return ret;
		} 
		bool mat_inv(){
			vector<int> is,js;
			is.resize(n,-1);
			js.resize(n,-1);
			for(int k=0;k<n;k++){
		        for(int i=k;i<n;i++)
		            for(int j=k;j<n;j++)if(a[i][j]){
		                is[k]=i,js[k]=j;break;
		            }
		        if(is[k]==-1||js[k]==-1) return 0;
		        for(int i=0;i<n;i++) // 2
		            swap(a[k][i],a[is[k]][i]);
		        for(int i=0;i<n;i++)
		            swap(a[i][k],a[i][js[k]]); 
		        if(!a[k][k]){
		        	return 0;
		        }
		        a[k][k]=inv(a[k][k]); 
		        for(int j=0;j<n;j++)if(j!=k)
		            (a[k][j]*=a[k][k])%=_mod;
		        for(int i=0;i<n;i++)if(i!=k)
		            for(int j=0;j<n;j++)if(j!=k)
		                (a[i][j]+=_mod-a[i][k]*a[k][j]%_mod)%=_mod;
		        for(int i=0;i<n;i++)
					if(i!=k)
		            	a[i][k]=(_mod-a[i][k]*a[k][k]%_mod)%_mod;            	
		    }
		    for(int k=n-1;k>=0;k--){
		        for(int i=0;i<n;i++)
		            swap(a[js[k]][i],a[k][i]);
		        for(int i=0;i<n;i++)
		            swap(a[i][is[k]],a[i][k]);
		    }
			return 1;
		}
	}; 
	
	vector<ll> fac,fac2;//factorial
	void fac_init(ll _size=maxn,ll _mod=mod){// x! factorial and init for arrangements and combinations 
		fac.resize(_size+1);
		fac[0]=1;
		for(ll i=1;i<=_size;i++)fac[i]=fac[i-1]*i%_mod;
	}
	void fac2_init(ll _size=maxn,ll _mod=mod){// x!!  
		fac2.resize(_size+1);
		fac2[0]=fac2[1]=1;
		for(ll i=2;i<=_size;i++)fac[i]=fac[i-2]*i%_mod;
	}
	ll arrangements(ll m,ll n,ll _mod=mod){//arrangements
		if(m<n) return 0;
		return fac[m]*inv(fac[m-n],_mod)%_mod;
	}
	ll combinations(ll m,ll n,ll _mod=mod){//combinations
		if(m<n) return 0;
		return fac[m]*inv(fac[n]*fac[m-n]%_mod,_mod)%_mod;
	}
	ll lucas_combinations(ll m,ll n,ll _mod=mod){
		if(n==0) return 1;
		return combinations(m%_mod,n%_mod,_mod)*(lucas_combinations(m/_mod,n/_mod,_mod))%_mod;
	}
	ll catalan(ll n,ll _mod=mod){//catalan(n)=catanlan(n-1)*(4n-2)/(n+1) 
		return (combinations(2*n,n)-combinations(2*n,n-1)+_mod)%_mod;
	}
	vector<int> prime,mpfactor,eular,mu;//prime,minimum prime factor,eular,mobius
	void prime_init(ll _size=maxn){//init for any prime sections 
		prime.resize(_size+1),mpfactor.resize(_size+1),eular.resize(_size+1),mu.resize(_size+1);
	    for (int i=0;i<=_size;i++) mpfactor[i]=i,eular[i]=i-1,mu[i]=0;
	    eular[0]=0,eular[1]=1,mu[1]=1;
		int tot=0;
	    for(int i=2;i<=_size;i++)
		{
	    	if(mpfactor[i]==i) prime[tot++]=i,mu[i]=-1;
	    	for(int j=0,t1;j<tot&&(t1=prime[j]*i)<=_size;j++)
	        {
	            mpfactor[t1]=prime[j];
	            if (i%prime[j]==0){
	            	eular[t1]=eular[i]*prime[j],mu[t1]=0;
					break;
				}
	            else eular[t1]=eular[i]*(prime[j]-1),mu[t1]=-mu[i];
	        }
		}
		prime.resize(tot);
	} 
	bool miller_rabin(ll n,int repeat=10){//check for big prime 
		if(n==2||n==3) return true;
		if(n<2||(n&1)==0) return false;
	    srand(time(NULL));
		ll d=n-1,s=__builtin_ctzll(d);
		d>>=s;
		while(repeat--){
	        ll a=qpow(rand()%(n-1)+1,d,n);
	    	if(a==1) continue;
	        for(int j=1;j<=s&&a!=1;j++)
	            a=mul(a,a,n);
	        if(a!=1) return false;
	    }
	    return true;
	}
	ll pollard_rho(ll n){//if x has more than a factor run this to looking for a factor
	    srand(time(NULL));
	    if(n==4)return 2;
	    while(1)
	    {
	        ll c=rand()%(n-1)+1;
	        ll t=c%n,r=(mul(t,t,n)+c)%n;
	        while (t!=r)
	        {
	            ll d=gcd(t-r,n);
	            if (d>1) return d;
	            t=(mul(t,t,n)+c)%n,r=(mul(r,r,n)+c)%n,r=(mul(r,r,n)+c)%n;
	        }
	    }
	}
	vector<ll> factor;
	void findfactor(ll n,bool flag=1)//finding 
	{
		if(flag)
		{
			factor.clear();
		    if(n<2) return;
		}
	    if(miller_rabin(n))
	    {
	        factor.push_back(n);
	        return;
	    }
	    ll p=n;
	    while(p>=n)p=pollard_rho(p);
	    findfactor(p,0);
	    findfactor(n/p,0);
	}
	
	
	ll poly_sz;
	vector<int> pos;
	ll ntt_mod=998244353,ntt_g=3;
	ll fwt_mod=998244353;
	void polynomial_init(int init_size=maxn){
		int j=-1;
		for(poly_sz=1;poly_sz<=init_size;poly_sz<<=1,j++);
		pos.resize(poly_sz);
		for(int i=0;i<poly_sz;i++) pos[i]=pos[i>>1]>>1|((i&1)<<j);
	}
	
	void fft(vector<Complex> &a,int opt){//opt=+-1
		a.resize(poly_sz);
		for(int i=0;i<poly_sz;i++) if(i<pos[i]) swap(a[i],a[pos[i]]);
		for(int i=1;i<poly_sz;i<<=1){
			Complex wn(cos(pi/i),opt*sin(pi/i));
			for(int j=0;j<poly_sz;j+=i<<1){
				Complex w(1,0);
				for(int k=0;k<i;k++,w=w*wn){
	                Complex p=a[j+k],q=w*a[j+k+i];
	                a[j+k]=p+q,a[j+k+i]=p-q;
	       		}
			}
		}
		if(opt==-1) for(int i=0;i<poly_sz;i++) a[i]=a[i]/Complex(poly_sz,0);
	}
	void fft_mul(vector<Complex> &a,vector<Complex> &b){
		for(int i=0;i<poly_sz;i++)
			a[i]=a[i]*b[i];
	}
	
	void ntt(vector<ll> &a,int opt)
	{
		a.resize(poly_sz);
		for(int i=0;i<poly_sz;i++) if(i<pos[i]) swap(a[i],a[pos[i]]);
		for(int i=1;i<poly_sz;i<<=1){
			ll gn=qpow(ntt_g,(ntt_mod-1)/(i<<1)*opt,ntt_mod);
			for(int j=0;j<poly_sz;j+=i<<1){
				ll g=1;
				for(int k=0;k<i;k++,g=g*gn%ntt_mod){
					ll p=a[j+k],q=g*a[j+k+i]%ntt_mod;
					a[j+k]=(p+q)%ntt_mod,a[j+k+i]=(p-q+ntt_mod)%ntt_mod;
				}
			}
		}
		if(opt==-1){
			ll invp=inv(poly_sz,ntt_mod); 
			for(int i=0;i<poly_sz;i++) a[i]=a[i]*invp%ntt_mod;
		}
	}
	void ntt_mul(vector<ll> &a,vector<ll> &b){
		for(int i=0;i<poly_sz;i++)
			a[i]=mul(a[i],b[i],ntt_mod);
	}
	void fwt_or(vector<ll> &a,int opt)
	{
		a.resize(poly_sz);
	    for(int i=1;i<poly_sz;i<<=1)
	        for(int p=i<<1,j=0;j<poly_sz;j+=p)
	            for(int k=0;k<i;++k)
	                if(opt==1)a[i+j+k]=(a[j+k]+a[i+j+k])%fwt_mod;
	                else a[i+j+k]=(a[i+j+k]+fwt_mod-a[j+k])%fwt_mod;
	}
	void fwt_and(vector<ll> &a,int opt)
	{
		a.resize(poly_sz);
	    for(int i=1;i<poly_sz;i<<=1)
	        for(int p=i<<1,j=0;j<poly_sz;j+=p)
	            for(int k=0;k<i;++k)
	                if(opt==1)a[j+k]=(a[j+k]+a[i+j+k])%fwt_mod;
	                else a[j+k]=(a[j+k]+fwt_mod-a[i+j+k])%fwt_mod;
	}
	void fwt_xor(vector<ll> &a,int opt)
	{
		a.resize(poly_sz);
	    for(int i=1;i<poly_sz;i<<=1)
	        for(int p=i<<1,j=0;j<poly_sz;j+=p)
	            for(int k=0;k<i;++k)
	            {
	                int X=a[j+k],Y=a[i+j+k];
	                a[j+k]=(X+Y)%fwt_mod;a[i+j+k]=(X+fwt_mod-Y)%fwt_mod;
	                if(opt==-1)a[j+k]=1ll*a[j+k]*inv(2,fwt_mod)%fwt_mod,a[i+j+k]=1ll*a[i+j+k]*inv(2,fwt_mod)%fwt_mod;
	            }
	}
	void fwt_mul(vector<ll> &a,vector<ll> &b){
		for(int i=0;i<poly_sz;i++)
			a[i]=mul(a[i],b[i],fwt_mod);
	}
	
	ll excrt(vector<ll> m, vector<ll> r){//return x requires x%[m]=[r] 
		assert(m.size()==r.size());
		ll mi=m[0],ri=r[0],x,y,d;
	    for (int i=1;i<(int)m.size();i++)
	    {
			d=exgcd(mi,m[i],x,y);
			if ((r[i]-ri)%d) return -1;
			x=(r[i]-ri)/d*x%(m[i]/d);
			ri+=x*mi;
			mi=mi/d*m[i];
			ri%=mi;
	    }
	    return ri>0?ri:ri+mi;
	}
	ll ex_bsgs(ll y,ll z,ll p)// y^x=z _mod p  if no solution return -1 
	{
		y%=p,z%=p;
		if(z==1)
			return 0;
		ll k=0,a=1;
		while(1)
		{
			ll d=gcd(y,p);
			if(d==1)break;
			if(z%d) return -1;
			z/=d,p/=d,++k,a=a*y/d%p;
			if(z==a) return k;
		}
		
		unordered_map<int,int> hash;
		hash.clear();
		int m=sqrt(p)+1;
		for(ll i=0,t=z;i<m;i++,t=t*y%p) hash[t]=i;
		for(ll i=1,tt=qpow(y,m,p),t=a*tt%p;i<=m;i++,t=t*tt%p)
		{
			if(hash.count(t)==0) continue;
			return i*m-hash[t]+k;
		}
		return -1;
	}
	
	/**
	vector<equation>
	equation: ai0 ai1 ai2 ...=bi
	**/
	vector<ll> gauss_x;   //vector<double> gauss_x;
	vector<bool> free_x;
	int gauss(vector<vector<ll> > &a,ll _mod=mod)//det equals to the product of main diagonal,rank equals to equ-gauss(which is number of free x)
	//int gauss(vector<vector<double> > &a)
	{
		int equ=a.size(),var=a[0].size()-1;
	    int max_r,col=0;
		int i,j,k;
		free_x.resize(var+1);
		gauss_x.resize(var+1);
	    for(int i=0;i<=var;i++)
	        gauss_x[i]=0,free_x[i]=true;
	    for(k=0;k<equ&&col<var;k++,col++){
	        max_r=k;
	        for(i=k+1;i<equ;i++)
	            if(abs(a[i][col])>abs(a[max_r][col])) max_r=i;
	        if(max_r!=k)
	            for(j=k;j<var+1;j++) swap(a[k][j],a[max_r][j]);
	        if(a[k][col]==0){
	            k--;
	            continue;
	        }
	        for(i=k+1;i<equ;i++)
	            if(a[i][col]!=0)
	            {
	                ll ta=a[k][col];
	                ll tb=a[i][col];
	//				double ta=a[k][col]/a[i][col];
	//				double tb=1.0;
	                for(j=col;j<var+1;j++)
	                    a[i][j]=a[i][j]*ta-a[k][j]*tb,
	                    ((a[i][j]%=_mod)+=_mod)%=_mod;   //
	            }
	    }
	    for(i=k;i<equ;i++)
	        if (a[i][col]!=0) 
				return -1;
	    if(k<var){
		    int free_x_num=0,free_index=0;
	        for (i=k-1;i>=0;i--){
	            for (j=0;j<var;j++)
	                if (a[i][j]!=0&&free_x[j]) 
						free_x_num++,free_index = j;
	            if (free_x_num>1) continue;
	            ll temp=a[i][var];
	            for (j=0;j<var;j++)
	                if (a[i][j]!=0&&j!=free_index) 
						temp-=a[i][j]*gauss_x[j],
						((temp%=_mod)+=_mod)%=_mod;   //
	            gauss_x[free_index] = temp*inv(a[i][free_index]);   
	//			gauss_x[free_index] = temp/a[i][free_index];
	            free_x[free_index]=0;
	        }
	        return var-k;
	    }
	    for (i=var-1;i>=0;i--) 
	    {
	        ll temp=a[i][var];  
	//		double temp=a[i][var];
	        for (j=i+1;j<var;j++)
	            if (a[i][j]!=0) 
					temp-=a[i][j]*gauss_x[j],
					((temp%=_mod)+=_mod)%=_mod;  //
	        gauss_x[i]=temp*inv(a[i][i]),
	        gauss_x[i]%=_mod;    //
	// 		gauss_x[i]=temp/a[i][i];
	    }
	    return 0;
	}
	
}	








#include<bits/stdc++.h>
using namespace geo;
using namespace mat;
int main()
{
	Polygon p;
	cin>>p;
	double ans=p.rotate_calipers(); 
	ans*=ans; 
	cout<<(ll)(ans+0.5)<<endl;
}

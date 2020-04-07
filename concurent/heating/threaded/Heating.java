class Heating {

	private final int n, m;
	private double[][] current, next;
	private final double r;

	public Heating( int n, int m, double r ){
		this.n = n;
		this.m = m;
		this.r = r;
		current = new double[n][m];  // initialized to 0.0
		next = new double[n][m];
		/*
		for(int i=0; i<m; ++i){
			next[0][i] = current[0][i] = 20.0;     // top row
			next[n-1][i] = current[n-1][i] = 20.0;     // bottom row
		}
		*/
		next[0][m/2] = current[0][m/2] = 100.0;     // middle of top row
	}

	class Calculate extends Thread {
		private final int index;
		Calculate(int i) {
			this.index = i;
		}
		@Override
		public void run() {
			for( int j=1; j<m-1; ++j ){
				next[index][j] = calculate_point(index, j, current);
			}
			return;
		}
	};

	public double calculate_point(int i, int j, double current[][]){
		return current[i][j]*(1.0-4.0*r) + r*(current[i][j-1]+current[i][j+1]+current[i+1][j]+current[i-1][j]);
	}

	public void step(){
		try {
		Thread threads[] = new Thread[n];
		final int thread_no = 20;
		for( int i=1; i<n-1; i+=thread_no ){
			//System.out.println("thread pool ");
			for (int k = 1; k < thread_no-1 && i+k < n-1; ++k){
				//System.out.println("thread " + (i+k-1));
				threads[i+k-1] = new Calculate(i+k-1);
				threads[i+k-1].start();
			}
			for (int k=1; k<thread_no-1 && i+k < n-1; ++k){
				threads[i+k-1].join();
			}
			//System.out.println("thread pool end");
		}
		}
		catch (InterruptedException ex) {
		}
		swap();
	}

	private void swap(){
		double[][] tmp = current;
		current = next;
		next = tmp;
	}

	public void iterate( int steps ){
		while( steps > 0 ){
			step();
			--steps;
		}
	}

	public double heat( int i, int j ){
		return current[i][j];
	}

	public void print(){
		for( int i=0; i<n; ++i ){
			for( int j = 0; j<m; ++j ){
				System.out.print(current[i][j]);
				System.out.print("\t");
			}
			System.out.println();
		}
	}

	public static void main( String[] args ){
		int size = args.length > 0 ? Integer.parseInt(args[0]) : 128;
		int iterations = args.length > 1 ? Integer.parseInt(args[1]) : 100000;
		Heating h = new Heating(size,size,0.2);
		h.iterate(iterations);
		//System.out.println(h.heat(12,512));
		h.print();
	}
}


/*
 *
 * java Heating >plot.txt
 * gnuplot
 *
  set xrange [0:128]
  set yrange [0:128]
  set zrange [0:128]
  splot 'plot.txt' matrix with lines notitle
*/
